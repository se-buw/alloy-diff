package org.alloytools.alloy.diff;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Expr;

/**
 * Holds a single constraint conjunct with metadata about its origin.
 * Used to track individual constraints added during module merging
 * so they can be evaluated against a diff witness for explanation.
 *
 * <p>
 * {@link #expr()} is the constraint as it is handed to the solver, i.e. it
 * refers to the <em>merged</em> signatures and fields and can be evaluated
 * against a diff witness. {@link #pos()} on the other hand must always point
 * into the <em>original</em> source file, because that is what gets
 * highlighted in the editor. The two are not always derivable from each other:
 * merged signatures carry positions from either version (or none at all), and
 * {@link Expr#span()} merges positions without checking that they come from
 * the same file. Producers of synthesized constraints should therefore pass an
 * explicit position, or {@link Pos#UNKNOWN} when the constraint has no
 * counterpart in the source.
 */
public record ConstraintInfo(
	/** The individual constraint expression (over merged sigs/fields) */
	Expr expr,
	/** Position in the original Alloy file, or Pos.UNKNOWN if synthesized */
	Pos pos,
	/** What kind of merge operation produced this constraint */
	ConstraintOrigin origin
) {

	public ConstraintInfo {
		if (pos == null) {
			pos = Pos.UNKNOWN;
		}
	}

	public ConstraintInfo(Expr expr, ConstraintOrigin origin) {
		this(expr, expr != null ? expr.pos() : Pos.UNKNOWN, origin);
	}

	/**
	 * True if {@link #pos()} can be used to highlight a region in an editor.
	 */
	public boolean hasSourcePos() {
		return pos != null && pos != Pos.UNKNOWN && pos.filename != null && !pos.filename.isEmpty() && pos.y > 0
				&& pos.x > 0;
	}

	/**
	 * Computes the source region to highlight for a conjunct taken verbatim from
	 * a parsed model.
	 * <p>
	 * Alloy wraps the body of a {@code fact} in one or more
	 * {@link edu.mit.csail.sdg.ast.ExprUnary.Op#NOOP} nodes whose position spans
	 * the <em>whole</em> {@code fact {...}} declaration, and
	 * {@code ExprList.make(AND, ...)} keeps those wrappers when it flattens
	 * conjunctions. Using {@code expr.pos()} directly therefore highlights the
	 * entire declaration instead of the offending conjunct. Unwrapping the NOOPs
	 * first and then taking {@link Expr#span()} yields exactly the text of the
	 * conjunct (e.g. {@code all n: Node | lone n.edges}), without unrolling the
	 * quantifier.
	 * <p>
	 * Only call this on expressions that come straight out of the parser — after
	 * {@code ModuleMerger.replaceSigRefs(..)} a span may mix positions from both
	 * compared files, which {@link Pos#merge(Pos)} does not guard against.
	 */
	public static Pos sourcePos(Expr expr) {
		if (expr == null) {
			return Pos.UNKNOWN;
		}
		Expr e = expr.deNOP();
		Pos span = e.span();
		if (span != null && span != Pos.UNKNOWN && span.filename != null && !span.filename.isEmpty() && span.y > 0) {
			return span;
		}
		Pos p = e.pos();
		return p == null ? Pos.UNKNOWN : p;
	}
}
