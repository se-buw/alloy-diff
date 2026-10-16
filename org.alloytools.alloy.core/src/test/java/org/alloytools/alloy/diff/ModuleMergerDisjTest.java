package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Regression tests for disj in field declarations (B9, 2026-10-14):
 * "disj f, g: e" (pairwise disjoint fields) and "f: disj e" (values of f
 * disjoint for different atoms), also for inherited fields, fields of subset
 * signatures, var fields, static disj fields of var signatures, and one
 * signatures (where Alloy adds no constraint for "f: disj e").
 * <p>
 * The expected results of the self-comparisons are those of the plain Alloy
 * Analyzer for each model: CommonInst(v, v) is satisfiable iff the command of v
 * is, and Equivalence(v, v) is never satisfiable.
 */
public class ModuleMergerDisjTest {

	private static final String DIR = "src/test/resources/disj/";

	private static boolean sat(String v1, String v2, Analysis a) {
		return ModuleDiff.diff(DIR + v1, DIR + v2, 0, 0, -1, true, a).satisfiable();
	}

	@Test
	public void commonInstancesOfSelfComparisonMatchAlloy() {
		assertEquals("dj1.als", true, sat("dj1.als", "dj1.als", Analysis.CommonInst));
		assertEquals("dj2.als", true, sat("dj2.als", "dj2.als", Analysis.CommonInst));
		assertEquals("dj3.als", true, sat("dj3.als", "dj3.als", Analysis.CommonInst));
		assertEquals("dj4.als", true, sat("dj4.als", "dj4.als", Analysis.CommonInst));
		assertEquals("dj5.als", false, sat("dj5.als", "dj5.als", Analysis.CommonInst));
		assertEquals("dj6.als", false, sat("dj6.als", "dj6.als", Analysis.CommonInst));
		assertEquals("inh1.als", false, sat("inh1.als", "inh1.als", Analysis.CommonInst));
		assertEquals("inh1b.als", true, sat("inh1b.als", "inh1b.als", Analysis.CommonInst));
		assertEquals("inh2.als", false, sat("inh2.als", "inh2.als", Analysis.CommonInst));
		assertEquals("sub1.als", false, sat("sub1.als", "sub1.als", Analysis.CommonInst));
		assertEquals("sub2.als", false, sat("sub2.als", "sub2.als", Analysis.CommonInst));
		assertEquals("tv1.als", false, sat("tv1.als", "tv1.als", Analysis.CommonInst));
		assertEquals("tv1b.als", true, sat("tv1b.als", "tv1b.als", Analysis.CommonInst));
		assertEquals("tv2.als", false, sat("tv2.als", "tv2.als", Analysis.CommonInst));
		assertEquals("tv3.als", false, sat("tv3.als", "tv3.als", Analysis.CommonInst));
		assertEquals("tv4.als", true, sat("tv4.als", "tv4.als", Analysis.CommonInst));
		assertEquals("one1.als", true, sat("one1.als", "one1.als", Analysis.CommonInst));
	}

	@Test
	public void selfComparisonIsEquivalent() {
		assertEquals("dj1.als", false, sat("dj1.als", "dj1.als", Analysis.Equivalence));
		assertEquals("dj2.als", false, sat("dj2.als", "dj2.als", Analysis.Equivalence));
		assertEquals("dj3.als", false, sat("dj3.als", "dj3.als", Analysis.Equivalence));
		assertEquals("dj4.als", false, sat("dj4.als", "dj4.als", Analysis.Equivalence));
		assertEquals("dj5.als", false, sat("dj5.als", "dj5.als", Analysis.Equivalence));
		assertEquals("dj6.als", false, sat("dj6.als", "dj6.als", Analysis.Equivalence));
		assertEquals("inh1.als", false, sat("inh1.als", "inh1.als", Analysis.Equivalence));
		assertEquals("inh1b.als", false, sat("inh1b.als", "inh1b.als", Analysis.Equivalence));
		assertEquals("inh2.als", false, sat("inh2.als", "inh2.als", Analysis.Equivalence));
		assertEquals("sub1.als", false, sat("sub1.als", "sub1.als", Analysis.Equivalence));
		assertEquals("sub2.als", false, sat("sub2.als", "sub2.als", Analysis.Equivalence));
		assertEquals("tv1.als", false, sat("tv1.als", "tv1.als", Analysis.Equivalence));
		assertEquals("tv1b.als", false, sat("tv1b.als", "tv1b.als", Analysis.Equivalence));
		assertEquals("tv2.als", false, sat("tv2.als", "tv2.als", Analysis.Equivalence));
		assertEquals("tv3.als", false, sat("tv3.als", "tv3.als", Analysis.Equivalence));
		assertEquals("tv4.als", false, sat("tv4.als", "tv4.als", Analysis.Equivalence));
		assertEquals("one1.als", false, sat("one1.als", "one1.als", Analysis.Equivalence));
	}

	@Test
	public void disjFieldsRemoveInstances() {
		// instances of the version without disj that violate disj
		assertEquals(true, sat("dj1.als", "dj2.als", Analysis.SemDiff));
		assertEquals(false, sat("dj2.als", "dj1.als", Analysis.SemDiff));
		assertEquals(true, sat("dj1.als", "dj2.als", Analysis.Equivalence));
		assertEquals(true, sat("dj3.als", "dj4.als", Analysis.SemDiff));
		assertEquals(false, sat("dj4.als", "dj3.als", Analysis.SemDiff));
	}

	@Test
	public void disjOfInheritedField() {
		assertEquals(true, sat("inh1.als", "inh1b.als", Analysis.SemDiff));
		assertEquals(false, sat("inh1b.als", "inh1.als", Analysis.SemDiff));
	}

	@Test
	public void disjOfVarFieldHoldsInEveryState() {
		assertEquals(true, sat("tv1.als", "tv1b.als", Analysis.SemDiff));
		assertEquals(false, sat("tv1b.als", "tv1.als", Analysis.SemDiff));
	}
}
