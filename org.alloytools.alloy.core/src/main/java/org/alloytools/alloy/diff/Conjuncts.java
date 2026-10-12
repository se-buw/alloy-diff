package org.alloytools.alloy.diff;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprList;

/**
 * Splits a formula into its top-level conjuncts.
 *
 * <p>
 * This is the granularity at which constraints are tracked and explained: it
 * is the finest level available without unrolling quantifiers. Alloy's
 * implicit conjunction inside a {@code fact { ... }} or a signature fact block
 * is flattened by the abstract syntax, so each constraint in a block becomes
 * its own conjunct and can be reported separately.
 *
 * <p>
 * Splitting must be done on the expression as it comes out of the parser, not
 * on the version rewritten over merged signatures: only the former has
 * positions that all point into a single source file.
 */
final class Conjuncts {

	private Conjuncts() {
	}

	/**
	 * The top-level conjuncts of {@code expr} in source order, with "true"
	 * dropped. The returned expressions are the original nodes, including any
	 * NOOP wrappers Alloy put around them, so they can be compared by identity
	 * against the conjuncts of another expression.
	 */
	static List<Expr> of(Expr expr) {
		List<Expr> out = new ArrayList<>();
		flatten(expr, out);
		return out;
	}

	/**
	 * A membership set over the given conjuncts using reference equality, for
	 * recognising the same Expr instance in two different formulas (e.g. the
	 * global facts inside a Command.formula).
	 */
	static Set<Expr> identitySet(List<Expr> conjuncts) {
		Set<Expr> set = Collections.newSetFromMap(new IdentityHashMap<>());
		set.addAll(conjuncts);
		return set;
	}

	private static void flatten(Expr expr, List<Expr> out) {
		if (expr == null) {
			return;
		}
		Expr x = expr.deNOP();
		if (x.isSame(ExprConstant.TRUE)) {
			return;
		}
		if (x instanceof ExprList && ((ExprList) x).op == ExprList.Op.AND) {
			for (Expr arg : ((ExprList) x).args) {
				flatten(arg, out);
			}
			return;
		}
		if (x instanceof ExprBinary && ((ExprBinary) x).op == ExprBinary.Op.AND) {
			flatten(((ExprBinary) x).left, out);
			flatten(((ExprBinary) x).right, out);
			return;
		}
		out.add(expr);
	}
}
