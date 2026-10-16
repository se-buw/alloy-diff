package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.CommandScope;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
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
	 *                 overriden by min(manual scope, default scope).
	 *                 -1 means: no explicit maximum. If withPred==true the scopes
	 *                 of the original commands are used as they are (as the
	 *                 Alloy Analyzer would use them for each model); otherwise
	 *                 Alloy's default scope of 3 is used.
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

		// Use the bitwidth Alloy uses for the original command(s): the bitwidth given
		// in the command (e.g. "for 3 but 6 Int") or Alloy's default otherwise.
		// Integer literals of the models are then interpreted (including overflow)
		// exactly as Alloy interprets them for the original models. The bitwidth is
		// only increased if needed to represent the scope bounds that are added as
		// cardinality constraints below (largest bound in maxInt).
		// (Previously the bitwidth started at 0 and only took the literals of
		// signature facts and field bounds into account, but not those of facts and
		// command predicates, which led to overflows that Alloy would not have.)
		int maxInt = 0;
		int bitwidth = Math.max(originalBitwidth(withPred ? cmd1 : null), originalBitwidth(withPred ? cmd2 : null));

		// scope -1: no maximum is requested, the scopes of the original commands are
		// used as they are (previously -1 silently became a maximum of 3, so e.g. a
		// "for 5" command was compared at scope 3)
		boolean capScopes = scope != -1;
		if (scope == -1) {
			scope = 3;
		}

		int maxseq1 = cmd1 != null ? cmd1.maxseq : -1;
		int maxseq2 = cmd2 != null ? cmd2.maxseq : -1;
		int maxseq = Math.max(maxseq1, maxseq2);

		// Steps (lengths of lasso traces), as Alloy's ScopeComputer computes them for
		// each version on its own: a version that is not temporal has no steps, and a
		// temporal version without a steps scope uses 1..10 steps. As for scopes and
		// bitwidth, the steps of the selected commands are only used with withPred.
		// (Previously the maxima of cmd1.maxprefix/cmd2.maxprefix were taken, so a
		// version without a steps scope (default 10) was analyzed with the smaller
		// steps scope of the other version.)
		boolean temporal1 = isTemporalVersion(v1, m.v1Sigs.values(), cmd1);
		boolean temporal2 = isTemporalVersion(v2, m.v2Sigs.values(), cmd2);
		int maxSteps1 = maxSteps(temporal1, withPred ? cmd1 : null);
		int maxSteps2 = maxSteps(temporal2, withPred ? cmd2 : null);
		int minSteps1 = minSteps(temporal1, withPred ? cmd1 : null, maxSteps1);
		int minSteps2 = minSteps(temporal2, withPred ? cmd2 : null, maxSteps2);
		// -1 if neither version is temporal
		int maxprefix = Math.max(maxSteps1, maxSteps2);
		int minprefix = Math.max(minSteps1, minSteps2);
		
		edu.mit.csail.sdg.ast.ExprVar commandKeyword = (cmd1 != null && cmd1.commandKeyword != null) ? cmd1.commandKeyword : ((cmd2 != null && cmd2.commandKeyword != null) ? cmd2.commandKeyword : edu.mit.csail.sdg.ast.ExprVar.make(null, "run"));

		// The command for computing signature scopes carries no steps: signature
		// scopes do not depend on steps, and Alloy rejects a steps scope for a
		// version that is not temporal ("You cannot set a scope on steps in static
		// models"), e.g., when a temporal version is compared with a static one.
		Command cmd4scope = new Command(edu.mit.csail.sdg.alloy4.Pos.UNKNOWN, ExprConstant.TRUE, "", false, scope, -1, maxseq, -1, -1, -1, null, null, commandKeyword, ExprConstant.TRUE, null);
		MyScopeComputer sc1 = MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd4scope);
		MyScopeComputer sc1orig = cmd1 != null ? MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v1Sigs.values(), cmd1) : sc1;
		MyScopeComputer sc2 = MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd4scope);
		MyScopeComputer sc2orig = cmd2 != null ? MyScopeComputer.compute(new A4Reporter(), new A4Options(), m.v2Sigs.values(), cmd2) : sc2;
		if (!withPred) {
			sc1orig = sc1;
			sc2orig = sc2;
		} else if (!capScopes) {
			// no maximum: min(sc, sc_orig) below must be the scope of the original
			// command (the default scope of 3 applies to a version without command)
			sc1 = sc1orig;
			sc2 = sc2orig;
		}

		// restrict union of children to scope of parent in v1
		for (Sig parent : m.v1iu.getParentSigs()) {
			Expr union = null;
			int ones = 0;
			boolean mutableUnion = false;
			for (Sig child : m.v1iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					mutableUnion |= s.isVariable != null;
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
					mutableUnion |= p.isVariable != null;
				}

				int scopeInOrig = Math.min(sc1.sig2scope(parent), sc1orig.sig2scope(parent));
				Expr scopeConstraint;
				if (sc1orig.isExact(parent) || (cmd1 != null && cmd1.additionalExactScopes.contains(parent))) {
					scopeConstraint = union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				} else {
					scopeConstraint = atMost(union, Math.max(ones, scopeInOrig), mutableUnion);
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
			boolean mutableUnion = false;
			for (Sig child : m.v2iu.getSubSigs(parent)) {
				Sig s = m.sigs.get(child.label);
				if (s != null) {
					mutableUnion |= s.isVariable != null;
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
					mutableUnion |= p.isVariable != null;
				}

				int scopeInOrig = Math.min(sc2.sig2scope(parent), sc2orig.sig2scope(parent));
				Expr scopeConstraint;
				if (sc2orig.isExact(parent) || (cmd2 != null && cmd2.additionalExactScopes.contains(parent))) {
					scopeConstraint = union.cardinality().equal(ExprConstant.makeNUMBER(Math.max(ones, scopeInOrig)));
				} else {
					scopeConstraint = atMost(union, Math.max(ones, scopeInOrig), mutableUnion);
				}
				m.trackConstraint(m.c2Constraints, scopeConstraint, scopePos(cmd2, parent), ConstraintOrigin.SCOPE_BOUND);
				c2 = c2.and(scopeConstraint);
				maxInt = Math.max(maxInt, Math.max(ones, scopeInOrig));
			}

		}

		for (Sig s : m.v1Sigs.values()) {
			maxInt = Math.max(maxInt, sc1.sig2scope(s));
		}
		for (Sig s : m.v2Sigs.values()) {
			maxInt = Math.max(maxInt, sc2.sig2scope(s));
		}
		// 30 is the largest bitwidth Alloy accepts
		while (maxInt > Util.max(bitwidth) && bitwidth < 30) {
			bitwidth++;
		}

		// The merged command explores traces with up to maxprefix steps. A temporal
		// version with a smaller maximum is restricted to the traces it has in Alloy,
		// i.e., to traces that have a lasso with at most maxStepsX states.
		if (temporal1 && maxSteps1 < maxprefix) {
			Expr lb = lassoBound(mutableRelations(), maxSteps1);
			if (lb != null) {
				m.trackConstraint(m.c1Constraints, lb, cmd1 != null && cmd1.pos != null ? cmd1.pos : Pos.UNKNOWN, ConstraintOrigin.SCOPE_BOUND);
				c1 = c1.and(lb);
			}
		}
		if (temporal2 && maxSteps2 < maxprefix) {
			Expr lb = lassoBound(mutableRelations(), maxSteps2);
			if (lb != null) {
				m.trackConstraint(m.c2Constraints, lb, cmd2 != null && cmd2.pos != null ? cmd2.pos : Pos.UNKNOWN, ConstraintOrigin.SCOPE_BOUND);
				c2 = c2.and(lb);
			}
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

			// Merged signatures are flat: for a signature with sub-signatures the scope
			// of the original module bounds the signature *together with* its
			// sub-signatures. That bound is already enforced by the
			// "union of children" constraints above. Bounding the flat merged
			// signature exactly would additionally force all sub-signatures to be
			// empty, so for such signatures the merged scope is only an upper bound
			// and no per-signature cardinality constraint is added.
			boolean hasSubSigs1 = s1 != null && m.v1iu.getSubSigs(s1) != null && !m.v1iu.getSubSigs(s1).isEmpty();
			boolean hasSubSigs2 = s2 != null && m.v2iu.getSubSigs(s2) != null && !m.v2iu.getSubSigs(s2).isEmpty();

			if (Math.max(scope1, scope2) >= 1) {
				// note that 0 can be computed if scope is too small for all subsignatures
				// however, if we restrict it, Alloy complains with an error
				// exact in the merged command only if both versions have the same exact
				// scope; otherwise, e.g., "exactly 3" vs "exactly 2", the version with
				// the smaller scope could not be represented (its "#s = 2" is in c1/c2)
				cmd = cmd.change(s, exact1 && exact2 && scope1 == scope2 && !hasSubSigs1 && !hasSubSigs2, Math.max(scope1, scope2));
			}
			// explicitly embed cardinality constraints to respect model scopes
			if (s1 != null && scope1 != -1 && !hasSubSigs1) {
				if (exact1) {
					Expr sc = s.cardinality().equal(ExprConstant.makeNUMBER(scope1));
					m.trackConstraint(m.c1Constraints, sc, scopePos(cmd1, s1), ConstraintOrigin.SCOPE_BOUND);
					c1 = c1.and(sc);
					changed = true;
				} else if (scope2 != -1 && scope1 < scope2) {
					Expr sc = atMost(s, scope1, s.isVariable != null);
					m.trackConstraint(m.c1Constraints, sc, scopePos(cmd1, s1), ConstraintOrigin.SCOPE_BOUND);
					c1 = c1.and(sc);
					changed = true;
				}
			}
			if (s2 != null && scope2 != -1 && !hasSubSigs2) {
				if (exact2) {
					Expr sc = s.cardinality().equal(ExprConstant.makeNUMBER(scope2));
					m.trackConstraint(m.c2Constraints, sc, scopePos(cmd2, s2), ConstraintOrigin.SCOPE_BOUND);
					c2 = c2.and(sc);
					changed = true;
				} else if (scope1 != -1 && scope2 < scope1) {
					Expr sc = atMost(s, scope2, s.isVariable != null);
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
	 * The scope bound "at most k atoms" for expression {@code e} (a signature or a
	 * union of signatures) of one version.
	 * <p>
	 * For a mutable expression the scope bounds the atoms that are in {@code e} in
	 * <em>any</em> state of the trace, not only in the first one: in Alloy the
	 * scope of a var sig bounds the pool of atoms the sig may use over time. "#e
	 * &lt;= k" would only constrain the first state. The bound is expressed as
	 * "there are no k+1 distinct atoms that are each in e at some state":
	 *
	 * <pre>
	 * not eventually (some x1: e | eventually (some x2: e - x1 | ... eventually some (e - x1 - ... - xk)))
	 * </pre>
	 *
	 * Picking the atoms in the order of a state in which each of them is in e,
	 * nested "eventually" (which includes the current state) suffices; quantified
	 * variables are rigid, i.e., denote the same atom in all states.
	 *
	 * @param mutable whether {@code e} may change over time
	 */
	static Expr atMost(Expr e, int k, boolean mutable) {
		if (!mutable) {
			return e.cardinality().lte(ExprConstant.makeNUMBER(k));
		}
		List<Decl> decls = new ArrayList<>();
		Expr dom = e;
		for (int i = 1; i <= k; i++) {
			Decl d = dom.oneOf("scope_x" + i);
			decls.add(d);
			dom = dom.minus(d.get());
		}
		Expr body = ExprUnary.Op.EVENTUALLY.make(null, dom.some());
		for (int i = k - 1; i >= 0; i--) {
			body = ExprUnary.Op.EVENTUALLY.make(null, ExprQt.Op.SOME.make(null, null, List.of(decls.get(i)), body));
		}
		return body.not();
	}

	/**
	 * Alloy's maximum number of steps when a temporal command does not specify
	 * one (see ScopeComputer).
	 */
	static final int DEFAULT_MAX_STEPS = 10;

	/**
	 * True if a version is temporal in the sense of Alloy
	 * (CompUtil.isTemporalModel): it has a mutable signature or field, or its
	 * command (or, without command, its facts) uses a temporal operator.
	 */
	static boolean isTemporalVersion(Module v, Iterable<Sig> sigs, Command cmd) {
		if (cmd != null) {
			return CompUtil.isTemporalModel(sigs, cmd);
		}
		for (Sig s : sigs) {
			if (s.isVariable != null) {
				return true;
			}
			for (Sig.Field f : s.getFields()) {
				if (f.isVariable != null) {
					return true;
				}
			}
		}
		return v.getAllReachableFacts().hasTemporal();
	}

	/**
	 * The maximum number of steps Alloy uses for a version: -1 if it is not
	 * temporal, the steps scope of the command, or the default of 10.
	 */
	static int maxSteps(boolean temporal, Command cmd) {
		if (!temporal) {
			return -1;
		}
		if (cmd != null && cmd.maxprefix >= 1) {
			return cmd.maxprefix;
		}
		return DEFAULT_MAX_STEPS;
	}

	/**
	 * The minimum number of steps Alloy uses for a version: -1 if it is not
	 * temporal, the minimum of the steps scope (at most the maximum), or 1.
	 */
	static int minSteps(boolean temporal, Command cmd, int maxSteps) {
		if (!temporal) {
			return -1;
		}
		if (cmd != null && cmd.minprefix >= 1) {
			return Math.min(cmd.minprefix, maxSteps);
		}
		return 1;
	}

	/**
	 * The mutable signatures and fields of the merged module.
	 */
	private List<Expr> mutableRelations() {
		List<Expr> rels = new ArrayList<>();
		for (Sig s : m.sigs.values()) {
			if (s.isVariable != null) {
				rels.add(s);
			}
			for (Sig.Field f : s.getFields()) {
				if (f.isVariable != null) {
					rels.add(f);
				}
			}
		}
		return rels;
	}

	/**
	 * A trace has a lasso with at most n states iff for some period p (1 &lt;= p
	 * &lt;= n) it repeats with period p from state n - p on:
	 *
	 * <pre>
	 * (after)^(n-1) always (R' = R)  or  (after)^(n-2) always (R'' = R)  or ...  or  always (R'...' = R)
	 * </pre>
	 *
	 * for all mutable relations R (with p primes). Static relations have the same
	 * value in all states. A lasso with prefix l and period p, l + p &lt;= n, also
	 * repeats with period p from state n - p &gt;= l on, and a trace that repeats
	 * with period p from state n - p on has a lasso with n states. Alloy's "n
	 * steps" counts the transitions including the looping one, i.e., the states of
	 * the lasso.
	 *
	 * @return the formula or null if there are no mutable relations
	 */
	static Expr lassoBound(List<Expr> rels, int n) {
		if (rels.isEmpty() || n < 1) {
			return null;
		}
		Expr res = null;
		for (int p = 1; p <= n; p++) {
			Expr eq = null;
			for (Expr r : rels) {
				Expr shifted = r;
				for (int i = 0; i < p; i++) {
					shifted = ExprUnary.Op.PRIME.make(null, shifted);
				}
				Expr e = shifted.equal(r);
				eq = (eq == null) ? e : eq.and(e);
			}
			Expr periodic = ExprUnary.Op.ALWAYS.make(null, eq);
			for (int i = 0; i < n - p; i++) {
				periodic = ExprUnary.Op.AFTER.make(null, periodic);
			}
			res = (res == null) ? periodic : res.or(periodic);
		}
		return res;
	}

	/**
	 * Alloy's integer bitwidth when a command does not specify one (see
	 * ScopeComputer).
	 */
	static final int DEFAULT_BITWIDTH = 4;

	/**
	 * The bitwidth Alloy uses when solving {@code cmd} on its own module: the
	 * bitwidth given in the command, or {@link #DEFAULT_BITWIDTH} if the command
	 * does not set one (or there is no command).
	 */
	static int originalBitwidth(Command cmd) {
		if (cmd != null && cmd.bitwidth >= 0) {
			return cmd.bitwidth;
		}
		return DEFAULT_BITWIDTH;
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
