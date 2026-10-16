package org.alloytools.alloy.diff;

/**
 * Categorizes the origin of a constraint added during module merging.
 */
public enum ConstraintOrigin {
	/** Multiplicity or attribute constraint on a signature (lone, one, some, abstract) */
	SIG_ATTRIBUTE,
	/** Subset sig hierarchy membership or equality constraint */
	SIG_HIERARCHY,
	/** Field bound / multiplicity constraint (all this: Sig | this.f in ...) */
	FIELD_MULTIPLICITY,
	/** Frame condition for a field that became variable */
	FIELD_FRAME,
	/** Disjointness of fields declared with disj (disj f, g: e or f: disj e) */
	FIELD_DISJOINT,
	/** User-defined signature fact */
	SIG_FACT,
	/** Closed-world constraint (sig.no() when sig is absent in one version) */
	CLOSED_WORLD,
	/** Global fact from the model */
	FACT,
	/** Predicate from a run/check command */
	COMMAND_PREDICATE,
	/** Scope / cardinality bound on a signature */
	SCOPE_BOUND
}
