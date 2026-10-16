package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

/**
 * Regression test for differing exact scopes (B10, 2026-10-14): "exactly 3 A"
 * vs "exactly 2 A" must not make the merged scope exactly 3.
 */
public class ModuleMergerExactScopeTest {

	private static final String DIR = "src/test/resources/scopes/";

	private static boolean sat(String v1, String v2, Analysis a) {
		return ModuleDiff.diff(DIR + v1, DIR + v2, 0, 0, -1, true, a).satisfiable();
	}

	@Test
	public void differentExactScopes() {
		// instances with exactly 2 A are not instances with exactly 3 A
		assertEquals(true, sat("exactly3.als", "exactly2.als", Analysis.SemDiff));
		assertEquals(true, sat("exactly2.als", "exactly3.als", Analysis.SemDiff));
		assertEquals(false, sat("exactly3.als", "exactly2.als", Analysis.CommonInst));
		assertEquals(false, sat("exactly2.als", "exactly2.als", Analysis.Equivalence));
	}
}
