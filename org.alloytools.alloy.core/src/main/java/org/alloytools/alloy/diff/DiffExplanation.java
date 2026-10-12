package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * Given a satisfiable diff witness (A4Solution), evaluates which constraints
 * from c1 or c2 are violated or satisfied.
 *
 * <p>
 * An explanation is always <em>relative to one witness</em>: the diff command
 * only asserts that <em>some</em> conjunct of the rejecting side is false, and
 * a different witness may well falsify a different conjunct. Use
 * {@link #explain(A4Solution, ModuleMerger, Analysis)} to obtain an
 * {@link Explanation} that remembers the witness it was computed for, so a
 * stale explanation can be detected with {@link Explanation#isFor(A4Solution)}
 * and recomputed after enumerating the next instance.
 *
 * <p>
 * To get a witness-independent answer — "this constraint is violated by
 * <em>every</em> instance in the difference" — use
 * {@link #isViolatedByEveryWitness}, which re-solves the diff command with the
 * constraint asserted.
 */
public class DiffExplanation {

	/**
	 * The violated constraints for one specific witness.
	 *
	 * @param witness    the solution this explanation was computed from; kept so
	 *                   callers can tell whether it still applies
	 * @param analysis   the analysis the witness came from
	 * @param violatedC1 constraints of the first model violated by the witness
	 * @param violatedC2 constraints of the second model violated by the witness
	 */
	public record Explanation(A4Solution witness, Analysis analysis, List<ConstraintInfo> violatedC1,
			List<ConstraintInfo> violatedC2) {

		/** True if this explanation was computed for exactly this solution. */
		public boolean isFor(A4Solution other) {
			return witness == other;
		}

		public boolean isEmpty() {
			return violatedC1.isEmpty() && violatedC2.isEmpty();
		}

		/**
		 * A witness of an asymmetric difference must violate at least one conjunct
		 * of the side it is excluded from. If it does not, some conjunct of that
		 * side was not tracked during merging and the explanation is incomplete
		 * rather than empty.
		 */
		public boolean isComplete() {
			if (analysis == Analysis.SemDiff) {
				return !violatedC1.isEmpty();
			}
			if (analysis == Analysis.Equivalence) {
				return !isEmpty();
			}
			return true;
		}
	}

	/**
	 * Computes the explanation for a witness.
	 *
	 * <p>
	 * For {@link Analysis#SemDiff} the command is {@code c2 and not c1}, so the
	 * witness satisfies c2 and violates c1: the violated c1 constraints are the
	 * reason the instance is rejected by the first model. For
	 * {@link Analysis#Equivalence} the command is {@code not (c1 iff c2)} and
	 * exactly one of the two sides is violated. For
	 * {@link Analysis#CommonInst} both sides hold, so there is nothing to
	 * explain.
	 */
	public static Explanation explain(A4Solution witness, ModuleMerger merger, Analysis analysis) {
		if (witness == null || !witness.satisfiable() || merger == null || analysis == null) {
			return new Explanation(witness, analysis, List.of(), List.of());
		}
		switch (analysis) {
		case SemDiff:
			return new Explanation(witness, analysis, getViolatedConstraints(witness, merger.getC1Constraints()),
					List.of());
		case Equivalence:
			return new Explanation(witness, analysis, getViolatedConstraints(witness, merger.getC1Constraints()),
					getViolatedConstraints(witness, merger.getC2Constraints()));
		case CommonInst:
		default:
			return new Explanation(witness, analysis, List.of(), List.of());
		}
	}

	/**
	 * Given a satisfiable diff witness, returns the list of constraints
	 * that are violated (evaluate to false) in the witness.
	 *
	 * @param witness     a satisfiable A4Solution
	 * @param constraints the list of constraints to evaluate (e.g., c1Constraints)
	 * @return the violated constraints (those evaluating to false)
	 */
	public static List<ConstraintInfo> getViolatedConstraints(A4Solution witness, List<ConstraintInfo> constraints) {
		return evaluate(witness, constraints, false);
	}

	/**
	 * Given a satisfiable diff witness, returns the list of constraints
	 * that are satisfied (evaluate to true) in the witness.
	 *
	 * @param witness     a satisfiable A4Solution
	 * @param constraints the list of constraints to evaluate
	 * @return the satisfied constraints (those evaluating to true)
	 */
	public static List<ConstraintInfo> getSatisfiedConstraints(A4Solution witness, List<ConstraintInfo> constraints) {
		return evaluate(witness, constraints, true);
	}

	private static List<ConstraintInfo> evaluate(A4Solution witness, List<ConstraintInfo> constraints,
			boolean keepIfTrue) {
		if (witness == null || !witness.satisfiable() || constraints == null) {
			return Collections.emptyList();
		}
		List<ConstraintInfo> result = new ArrayList<>();
		for (ConstraintInfo ci : constraints) {
			try {
				Object value = witness.eval(ci.expr());
				if (value instanceof Boolean && ((Boolean) value).booleanValue() == keepIfTrue) {
					result.add(ci);
				}
			} catch (Err e) {
				// If evaluation fails, skip this constraint
			}
		}
		return result;
	}

	/**
	 * Returns all source positions of violated constraints, suitable for
	 * highlighting in the Alloy Analyzer editor.
	 * Filters out unknown/synthetic positions.
	 *
	 * @param witness     a satisfiable A4Solution
	 * @param constraints the list of constraints to evaluate
	 * @return positions of violated constraints
	 */
	public static List<Pos> getViolatedPositions(A4Solution witness, List<ConstraintInfo> constraints) {
		return getViolatedConstraints(witness, constraints).stream()
				.filter(ConstraintInfo::hasSourcePos)
				.map(ConstraintInfo::pos)
				.collect(Collectors.toList());
	}

	/**
	 * For a violated conjunct that constrains mutable state, returns the first
	 * state of the trace at which it fails; -1 if the witness is not a trace or
	 * the conjunct is not state-local in the sense below.
	 *
	 * <p>
	 * Conjuncts that constrain mutable state are wrapped in {@code always} by the
	 * merge (see {@code ModuleMerger.alwaysIfVar}), so the conjunct alone says
	 * that the instance leaves the semantics of the model, but not <em>when</em>.
	 * Two shapes are produced: {@code always b} and
	 * {@code all x: S | always b} (field multiplicities and frame conditions).
	 * Both are turned into a state-local witness formula — {@code not b} and
	 * {@code some x: S | not b} respectively — which is then evaluated at each
	 * state of the finite prefix of the lasso. For a frame condition
	 * {@code always this.f' = this.f} the reported state is the source of the
	 * transition in which the field changes.
	 */
	public static int firstViolatingState(A4Solution witness, ConstraintInfo constraint) {
		if (witness == null || !witness.satisfiable() || !witness.isTemporal() || constraint == null) {
			return -1;
		}
		Expr probe;
		try {
			probe = stateLocalNegation(constraint.expr());
		} catch (Err e) {
			return -1;
		}
		if (probe == null) {
			return -1;
		}
		for (int state = 0; state < witness.getTraceLength(); state++) {
			try {
				Object value = witness.eval(probe, state);
				if (value instanceof Boolean && ((Boolean) value).booleanValue()) {
					return state;
				}
			} catch (Err e) {
				return -1;
			}
		}
		return -1;
	}

	/**
	 * Turns {@code always b} into {@code not b} and {@code all x: S | always b}
	 * into {@code some x: S | not b}; returns null for conjuncts that are not of
	 * either shape, i.e. that do not constrain mutable state.
	 */
	private static Expr stateLocalNegation(Expr constraint) throws Err {
		Expr e = constraint.deNOP();
		if (e instanceof ExprUnary && ((ExprUnary) e).op == ExprUnary.Op.ALWAYS) {
			return ((ExprUnary) e).sub.not();
		}
		if (e instanceof ExprQt && ((ExprQt) e).op == ExprQt.Op.ALL) {
			ExprQt qt = (ExprQt) e;
			Expr body = qt.sub.deNOP();
			if (body instanceof ExprUnary && ((ExprUnary) body).op == ExprUnary.Op.ALWAYS) {
				return ExprQt.Op.SOME.make(qt.pos, qt.closingBracket, qt.decls, ((ExprUnary) body).sub.not());
			}
		}
		return null;
	}

	/**
	 * Decides whether a constraint is violated by <em>every</em> instance in the
	 * difference, not just by the witness at hand. This is the witness-independent
	 * part of an explanation and does not become stale when the user asks for the
	 * next instance.
	 *
	 * <p>
	 * The check re-solves the diff command with the constraint asserted: if
	 * {@code diff and constraint} is unsatisfiable then no instance of the
	 * difference satisfies the constraint, i.e. all of them violate it.
	 *
	 * @param sigs        the merged signatures the diff command was solved with
	 * @param diffCommand the command produced by
	 *                    {@link CommandGenerator#generateDiffCommand}
	 * @param options     the solver options to use
	 * @param constraint  the constraint to test
	 * @return true if every witness of the difference violates the constraint
	 */
	public static boolean isViolatedByEveryWitness(Collection<Sig> sigs, Command diffCommand, A4Options options,
			ConstraintInfo constraint) {
		if (sigs == null || diffCommand == null || constraint == null) {
			return false;
		}
		try {
			Command probe = diffCommand.change(diffCommand.formula.and(constraint.expr()));
			A4Solution sol = TranslateAlloyToKodkod.execute_command(new A4Reporter(), sigs, probe,
					options == null ? new A4Options() : options);
			return !sol.satisfiable();
		} catch (Err e) {
			return false;
		}
	}

	/**
	 * Returns the source text a position refers to, for showing the offending
	 * conjunct next to the link in the log.
	 *
	 * @param pos     the position to read
	 * @param sources filename to file content (e.g. {@code ModuleDiff.sources})
	 * @return the source text, whitespace-collapsed, or an empty string
	 */
	public static String sourceText(Pos pos, Map<String,String> sources) {
		if (pos == null || pos == Pos.UNKNOWN || sources == null || pos.filename == null || pos.y < 1) {
			return "";
		}
		String content = sources.get(pos.filename);
		if (content == null) {
			return "";
		}
		String[] lines = content.split("\r\n|\r|\n", -1);
		if (pos.y > lines.length) {
			return "";
		}
		int lastLine = Math.min(pos.y2, lines.length);
		StringBuilder sb = new StringBuilder();
		for (int y = pos.y; y <= lastLine; y++) {
			String line = lines[y - 1];
			int from = (y == pos.y) ? Math.max(0, Math.min(pos.x - 1, line.length())) : 0;
			int to = (y == lastLine) ? Math.max(from, Math.min(pos.x2, line.length())) : line.length();
			sb.append(line, from, to);
			if (y < lastLine) {
				sb.append(' ');
			}
		}
		return sb.toString().replaceAll("\\s+", " ").trim();
	}
}
