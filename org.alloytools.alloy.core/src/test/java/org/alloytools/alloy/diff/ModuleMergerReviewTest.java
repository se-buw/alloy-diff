package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import edu.mit.csail.sdg.translator.A4Solution;

/**
 * Regression tests for defects found in an external review (2026-10-16). The
 * expected results are those of the plain Alloy Analyzer for the original
 * models (or follow directly from them, e.g., for identical semantics).
 * <p>
 * I1: the scope bound #(s1 + ... + sn) <= k of a hierarchy overflowed at the
 * bitwidth of the commands and then did not restrict a version to its scope.
 * I5: the bitwidth was increased for every signature scope, also without a
 * scope bound, which changed the integer semantics. I2: declaration constraints
 * were wrapped in always only if the declared signature or field was mutable,
 * not if the constraint refers to a mutable signature. I3: "sig S = T" with a
 * subset signature T became S = (type parents of T). I6: "f: A -> B" and
 * "f: set A -> B" were rejected as a mix of arities.
 * <p>
 * SemDiff of (v1, v2) computes the instances of v2 that are not instances of v1.
 */
public class ModuleMergerReviewTest {

	private static final String DIR = "src/test/resources/review/";

	private static A4Solution diff(String v1, String v2, Analysis a) {
		return ModuleDiff.diff(DIR + v1, DIR + v2, 0, 0, -1, true, a);
	}

	private static boolean sat(String v1, String v2, Analysis a) {
		return diff(v1, v2, a).satisfiable();
	}

	@Test
	public void i1HierarchyBoundDoesNotOverflow() {
		// 8 atoms of the flat model are not an instance of the hierarchy (scope 3)
		assertEquals(true, sat("i1_hier.als", "i1_flat.als", Analysis.SemDiff));
		assertEquals(true, sat("i1_hier_bw5.als", "i1_flat_bw5.als", Analysis.SemDiff));
		// both models have at most 3 colors
		assertEquals(false, sat("i1_colorAbstract.als", "i1_colorFlat.als", Analysis.Equivalence));
		// the model has no instance in its scope (8 atoms needed)
		assertEquals(false, sat("i1_same.als", "i1_same.als", Analysis.CommonInst));
		assertEquals(false, sat("i1_same.als", "i1_same.als", Analysis.Equivalence));
		// hierarchy with scope 3 or 7 vs. flat signatures with scope 10
		assertEquals(false, sat("i1_flat10.als", "i1_h3.als", Analysis.SemDiff));
		assertEquals(true, sat("i1_h3.als", "i1_flat10.als", Analysis.SemDiff));
		assertEquals(false, sat("i1_flat10.als", "i1_h7.als", Analysis.SemDiff));
	}

	@Test
	public void i1GuardedBoundKeepsBitwidth() {
		// the guarded bound needs no larger bitwidth for scope 3 vs. 10
		assertEquals(4, diff("i1_h3.als", "i1_flat10.als", Analysis.SemDiff).getBitwidth());
		// bound k = 7 plus scope 10 does not fit below 2^4, so the bitwidth is 5
		assertEquals(5, diff("i1_h7.als", "i1_flat10.als", Analysis.Equivalence).getBitwidth());
	}

	@Test
	public void i5BitwidthOnlyIncreasedForBounds() {
		// both "for 10": #A > 5 and #A > 5 and #A <= 7 are equivalent at bitwidth 4
		assertEquals(false, sat("i5_gt5.als", "i5_gt5le7.als", Analysis.Equivalence));
		assertEquals(4, diff("i5_gt5.als", "i5_gt5le7.als", Analysis.Equivalence).getBitwidth());
		// "#A <= 3" with up to 10 atoms of A in T(v1, v2) at bitwidth 4
		assertEquals(false, sat("i5_for10.als", "i5_for3.als", Analysis.SemDiff));
		assertEquals(true, sat("i5_for3.als", "i5_for10.als", Analysis.SemDiff));
		assertEquals(4, diff("i5_for3.als", "i5_for10.als", Analysis.SemDiff).getBitwidth());
	}

	@Test
	public void i2TemporalDeclarationsHoldInEveryState() {
		assertEquals(false, sat("i2_varFieldType_v1.als", "i2_varFieldType_v2.als", Analysis.Equivalence));
		assertEquals(false, sat("i2_fieldOfVarSubset_v1.als", "i2_fieldOfVarSubset_v2.als", Analysis.Equivalence));
		assertEquals(false, sat("i2_varSubsetParents_v1.als", "i2_varSubsetParents_v2.als", Analysis.Equivalence));
	}

	@Test
	public void i3ExactSubsetSigEqualsOriginalParents() {
		assertEquals(false, sat("i3_exactSubset_v1.als", "i3_exactSubset_v2.als", Analysis.Equivalence));
	}

	@Test
	public void i6SameArityDifferentSyntax() {
		assertEquals(false, sat("i6_arrow.als", "i6_setArrow.als", Analysis.Equivalence));
		assertEquals(false, sat("i6_setArrowOne.als", "i6_arrowOne.als", Analysis.Equivalence));
		// the arrow multiplicity after "set" is kept
		assertEquals(true, sat("i6_setArrowOne.als", "i6_arrow.als", Analysis.SemDiff));
		assertEquals(false, sat("i6_arrow.als", "i6_setArrowOne.als", Analysis.SemDiff));
	}
}
