package org.alloytools.alloy.diff;

import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.MyScopeComputer;

public class CommandGenerator {

	private ModuleMerger m;

	public CommandGenerator(ModuleMerger merger) {
		this.m = merger;
	}

	/**
	 * compute a run command for diff(v1, v2) = sem(v2) \ sem(v1)
	 * 
	 * @param v1
	 * @param v2
	 * @param scope    the maximum scope for comparison (might be overriden by Alloy
	 *                 due to inheitance), if withPred==true the scope will be
	 *                 overriden by min(manual scope, default scope)
	 * @param withPred take the predicate of the first command into account
	 *                 (otherwise only signatures and facts but ignores original
	 *                 command)
	 * @return
	 */
	public Command generateDiffCommand(Module v1, Module v2, int scope, boolean withPred, Analysis a) {
		return generateDiffCommand(v1, v2, 0, 0, scope, withPred, a);
	}

	public Command generateDiffCommand(Module v1, Module v2, int cmdIndex1, int cmdIndex2, int scope, boolean withPred, Analysis a) {

		Command cmd1 = (cmdIndex1 >= 0 && v1.getAllCommands().size() > cmdIndex1) ? v1.getAllCommands().get(cmdIndex1) : null;
		Command cmd2 = (cmdIndex2 >= 0 && v2.getAllCommands().size() > cmdIndex2) ? v2.getAllCommands().get(cmdIndex2) : null;

		int bitwidth = 0;
		int maxInt = m.maxInt;

		Expr c1 = null;
		Expr c2 = null;

		if (withPred && cmd1 != null && cmd2 != null) {
			// Command.formula is "globalFacts and predicateBody" (see
			// CompModule.resolveCommand), so split the facts back out to label them
			// correctly in the explanation.
			Expr pred1 = trackConjuncts(m.c1Constraints, cmd1.formula, true, ConstraintOrigin.COMMAND_PREDICATE,
					Conjuncts.identitySet(Conjuncts.of(v1.getAllReachableFacts())));
			Expr pred2 = trackConjuncts(m.c2Constraints, cmd2.formula, false, ConstraintOrigin.COMMAND_PREDICATE,
					Conjuncts.identitySet(Conjuncts.of(v2.getAllReachableFacts())));
			c1 = m.c1.and(pred1);
			c2 = m.c2.and(pred2);
		} else {
			Expr facts1 = trackConjuncts(m.c1Constraints, v1.getAllReachableFacts(), true, ConstraintOrigin.FACT, null);
			Expr facts2 = trackConjuncts(m.c2Constraints, v2.getAllReachableFacts(), false, ConstraintOrigin.FACT, null);
			c1 = m.c1.and(facts1);
			c2 = m.c2.and(facts2);
		}

		if (scope == -1) {
			scope = 3;
		}

		int maxseq1 = cmd1 != null ? cmd1.maxseq : -1;
		int minprefix1 = cmd1 != null ? cmd1.minprefix : -1;
		int maxprefix1 = cmd1 != null ? cmd1.maxprefix : -1;

		int maxseq2 = cmd2 != null ? cmd2.maxseq : -1;
		int minprefix2 = cmd2 != null ? cmd2.minprefix : -1;
		int maxprefix2 = cmd2 != null ? cmd2.maxprefix : -1;

		int maxseq = Math.max(maxseq1, maxseq2);
		int minprefix = Math.max(minprefix1, minprefix2);
		int maxprefix = Math.max(maxprefix1, maxprefix2);
		
		edu.mit.csail.sdg.ast.ExprVar commandKeyword = (cmd1 != null && cmd1.commandKeyword != null) ? cmd1.commandKeyword : ((cmd2 != null && cmd2.commandKeyword != null) ? cmd2.commandKeyword : edu.mit.csail.sdg.ast.ExprVar.make(null, "run"));

		Command cmd4scope = new Command(edu.mit.csail.sdg.alloy4.Pos.UNKNOWN, ExprConstant.TRUE, "", false, scope, -1, maxseq, minprefix, maxprefix, -1, null, null, commandKeyword, ExprConstant.TRUE, null);
		MyScopeComputer sc1 = MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd4scope);
		MyScopeComputer sc1orig = cmd1 != null ? MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd1) : sc1;
		MyScopeComputer sc2 = MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd4scope);
		MyScopeComputer sc2orig = cmd2 != null ? MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd2) : sc2;
		if (!withPred) {
			sc1orig = sc1;
			sc2orig = sc2;
		}

		// restrict union of children to scope of parent in v1
		for (Sig parent : m.v1iu.getParentSigs()) {
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v1iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					// ones override the default scope (important for enums!)
					if (s.isOne != null) {
						ones++;
					}
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}
				}
			}
			if (union != null) {
				Sig p = m.sigs.get(parent.label);
				if (p != null) {
					union = union.plus(p);
				}

				int scopeInOrig = Math.min(sc1.sig2scope(parent), sc1orig.sig2scope(parent));
				Expr scopeConstraint;
				if (sc1orig.isExact(parent) || (cmd1 != null && cmd1.additionalExactScopes.contains(parent))) {
					scopeConstraint = union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				} else {
					scopeConstraint = union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				}
				m.trackConstraint(m.c1Constraints, scopeConstraint, scopePos(cmd1, parent), ConstraintOrigin.SCOPE_BOUND);
				c1 = c1.and(scopeConstraint);
				maxInt = Math.max(maxInt, Math.max(ones, scopeInOrig));
			}
		}
		// restrict union of children to scope of parent in v2
		for (Sig parent : m.v2iu.getParentSigs()) {
			Expr union = null;
			int ones = 0;
			for (Sig child : m.v2iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					// ones override the default scope (important for enums!)
					if (s.isOne != null) {
						ones++;
					}
					if (union == null) {
						union = s;
					} else {
						union = union.plus(s);
					}
				}
			}
			if (union != null) {
				Sig p = m.sigs.get(parent.label);
				if (p != null) {
					union = union.plus(p);
				}

				int scopeInOrig = Math.min(sc2.sig2scope(parent), sc2orig.sig2scope(parent));
				Expr scopeConstraint;
				if (sc2orig.isExact(parent) || (cmd2 != null && cmd2.additionalExactScopes.contains(parent))) {
					scopeConstraint = union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				} else {
					scopeConstraint = union.cardinality().lte(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				}
				m.trackConstraint(m.c2Constraints, scopeConstraint, scopePos(cmd2, parent), ConstraintOrigin.SCOPE_BOUND);
				c2 = c2.and(scopeConstraint);
			}

		}

		for (Sig s : m.v1Sigs.values()) {
			maxInt = Math.max(maxInt, sc1.sig2scope(s));
		}
		for (Sig s : m.v2Sigs.values()) {
			maxInt = Math.max(maxInt, sc2.sig2scope(s));
		}
		while (maxInt > Util.max(bitwidth)) {
			bitwidth++;
		}

		Command cmd = new Command(edu.mit.csail.sdg.alloy4.Pos.UNKNOWN, getExpr(c1, c2, a), "", false, scope, bitwidth, maxseq, minprefix, maxprefix, -1, null, null, commandKeyword, getExpr(c1, c2, a), null);

		boolean changed = false;
		// update scope based on both modules
		for (String sName : m.sigs.keySet()) {
			Sig s = m.sigs.get(sName);

			Sig s1 = m.v1Sigs.get(sName);
			int scope1 = -1;
			boolean exact1 = cmd1 != null && cmd1.additionalExactScopes.contains(s1);
			if (s1 != null) {
				scope1 = Math.min(sc1.sig2scope(s1), sc1orig.sig2scope(s1));
				exact1 |= sc1orig.isExact(s1);
			}

			Sig s2 = m.v2Sigs.get(sName);
			int scope2 = -1;
			boolean exact2 = cmd2 != null && cmd2.additionalExactScopes.contains(s2);
			if (s2 != null) {
				scope2 = Math.min(sc2.sig2scope(s2), sc2orig.sig2scope(s2));
				exact2 |= sc2orig.isExact(s2);
			}

			if (Math.max(scope1, scope2) >= 1) {
				// note that 0 can be computed if scope is too small for all subsignatures
				// however, if we restrict it, Alloy complains with an error
				cmd = cmd.change(s, exact1 && exact2, Math.max(scope1, scope2));
			}
			// explicitly embed cardinality constraints to respect model scopes
			if (s1 != null && scope1 != -1) {
				if (exact1) {
					Expr sc = s.cardinality().equal(ExprConstant.makeNUMBER(scope1));
					m.trackConstraint(m.c1Constraints, sc, scopePos(cmd1, s1), ConstraintOrigin.SCOPE_BOUND);
					c1 = c1.and(sc);
					changed = true;
				} else if (scope2 != -1 && scope1 < scope2) {
					Expr sc = s.cardinality().lte(ExprConstant.makeNUMBER(scope1));
					m.trackConstraint(m.c1Constraints, sc, scopePos(cmd1, s1), ConstraintOrigin.SCOPE_BOUND);
					c1 = c1.and(sc);
					changed = true;
				}
			}
			if (s2 != null && scope2 != -1) {
				if (exact2) {
					Expr sc = s.cardinality().equal(ExprConstant.makeNUMBER(scope2));
					m.trackConstraint(m.c2Constraints, sc, scopePos(cmd2, s2), ConstraintOrigin.SCOPE_BOUND);
					c2 = c2.and(sc);
					changed = true;
				} else if (scope1 != -1 && scope2 < scope1) {
					Expr sc = s.cardinality().lte(ExprConstant.makeNUMBER(scope2));
					m.trackConstraint(m.c2Constraints, sc, scopePos(cmd2, s2), ConstraintOrigin.SCOPE_BOUND);
					c2 = c2.and(sc);
					changed = true;
				}
			}
		}

		if (changed) {
			cmd = cmd.change(getExpr(c1, c2, a));
		}

		return cmd;
	}
	/**
	 * Splits a source expression into its top-level conjuncts, rewrites each one
	 * over the merged signatures, tracks it for the explanation and returns the
	 * conjunction of the rewritten conjuncts.
	 * <p>
	 * The split is done on the <em>original</em> expression rather than on the
	 * rewritten one on purpose: only the original still has positions that all
	 * point into a single source file, so each conjunct can be given the exact
	 * source region it came from. Rewriting is compositional, so rewriting the
	 * conjuncts one by one is equivalent to rewriting the whole conjunction.
	 *
	 * @param list      the constraint list to append to (c1 or c2)
	 * @param expr      the original, un-rewritten expression
	 * @param inV1      whether to rewrite against v1 or v2
	 * @param origin    the origin to record for conjuncts that are not in
	 *                  {@code factConjuncts}
	 * @param factConjuncts conjuncts that are global facts (recorded as
	 *                  {@link ConstraintOrigin#FACT}), or null if none
	 */
	private Expr trackConjuncts(List<ConstraintInfo> list, Expr expr, boolean inV1, ConstraintOrigin origin,
			Set<Expr> factConjuncts) {
		Expr result = null;
		for (Expr conjunct : Conjuncts.of(expr)) {
			ConstraintOrigin o = (factConjuncts != null && factConjuncts.contains(conjunct)) ? ConstraintOrigin.FACT
					: origin;
			Expr rewritten = m.replaceSigRefs(conjunct, inV1);
			m.trackConstraint(list, rewritten, ConstraintInfo.sourcePos(conjunct), o);
			result = (result == null) ? rewritten : result.and(rewritten);
		}
		return result == null ? ExprConstant.TRUE : result;
	}

	/**
	 * The source position to blame for a scope bound on {@code s}: the explicit
	 * scope in the command if there is one, otherwise the command itself.
	 */
	private static Pos scopePos(Command cmd, Sig s) {
		if (cmd == null) {
			return Pos.UNKNOWN;
		}
		if (s != null && cmd.scope != null) {
			for (CommandScope cs : cmd.scope) {
				if (cs.sig != null && cs.sig.label.equals(s.label)) {
					return cs.pos != null ? cs.pos : Pos.UNKNOWN;
				}
			}
		}
		return cmd.pos == null ? Pos.UNKNOWN : cmd.pos;
	}

	private Expr getExpr(Expr c1, Expr c2, Analysis a) {
		switch (a) {
		case SemDiff:
			return c2.and(c1.not());
		case CommonInst:
			return c1.and(c2);
		case Equivalence:
			return c1.iff(c2).not();

		default:
			break;
		}
		return ExprConstant.TRUE;
	}

	public Command generateCommand(Module v1, Module v2, int scope, boolean withPred, Expr customFormula) {
		Command baseCmd = generateDiffCommand(v1, v2, scope, withPred, Analysis.CommonInst);
		return baseCmd.change(customFormula);
	}

}
