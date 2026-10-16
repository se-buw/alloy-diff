package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import edu.mit.csail.sdg.translator.A4Solution;

/**
 * Regression tests for the handling of steps (trace lengths) and of the
 * multiplicities of common signatures (2026-10-14).
 * <p>
 * grow3/grow4: a trace with #S = 3 needs 4 states, so grow3 (3 steps) has no
 * instance and grow4 (4 steps) has one. grow5def (default 10 steps) and
 * grow5_4 (4 steps) need 6 states. osc2/osc3/osc23 need a lasso of 3 states
 * that loops back to state 1.
 */
public class ModuleMergerStepsTest {

	private static final String DIR = "src/test/resources/steps/";

	private static boolean sat(String v1, String v2, Analysis a) {
		A4Solution s = ModuleDiff.diff(DIR + v1, DIR + v2, 0, 0, -1, true, a);
		return s.satisfiable();
	}

	@Test
	public void smallerMaxStepsIsRespected() {
		// grow3 has no instance, so there is no common instance
		assertEquals(false, sat("grow3.als", "grow4.als", Analysis.CommonInst));
		assertEquals(true, sat("grow3.als", "grow4.als", Analysis.Equivalence));
		// sem(grow3) is empty, so grow3 and not grow4 has no instance
		assertEquals(false, sat("grow4.als", "grow3.als", Analysis.SemDiff));
	}

	@Test
	public void defaultStepsAreNotReducedByOtherVersion() {
		assertEquals(true, sat("grow5def.als", "grow5_4.als", Analysis.Equivalence));
		// grow5def and not grow5_4
		assertEquals(true, sat("grow5_4.als", "grow5def.als", Analysis.SemDiff));
	}

	@Test
	public void lassoWithEarlierLoopState() {
		assertEquals(false, sat("osc2.als", "osc3.als", Analysis.CommonInst));
		assertEquals(true, sat("osc2.als", "osc3.als", Analysis.Equivalence));
		// the minimum number of steps does not change the set of traces
		assertEquals(false, sat("osc23.als", "osc3.als", Analysis.Equivalence));
	}

	@Test
	public void selfComparisonsMatchAlloy() {
		assertEquals(false, sat("grow3.als", "grow3.als", Analysis.CommonInst));
		assertEquals(true, sat("grow4.als", "grow4.als", Analysis.CommonInst));
		assertEquals(false, sat("grow4.als", "grow4.als", Analysis.Equivalence));
		assertEquals(false, sat("osc2.als", "osc2.als", Analysis.CommonInst));
		assertEquals(true, sat("osc3.als", "osc3.als", Analysis.CommonInst));
	}

	@Test
	public void stepsScopeWithStaticVersionDoesNotCrash() {
		// previously: "You cannot set a scope on steps in static models"
		assertEquals(true, sat("sentVar5steps.als", "sentStatic.als", Analysis.SemDiff));
		assertEquals(false, sat("sentStatic.als", "sentVar5steps.als", Analysis.CommonInst));
	}

	@Test
	public void leastUpperBoundOfSigMultiplicities() {
		ModuleMerger m = new ModuleMerger();
		m.mergeSigs(edu.mit.csail.sdg.parser.CompUtil.parseEverything_fromFile(null, null, DIR + "multOne.als"),
				edu.mit.csail.sdg.parser.CompUtil.parseEverything_fromFile(null, null, DIR + "multLone.als"));
		assertEquals(true, m.sigs.get("this/A").isLone != null);
		// the original multiplicities still distinguish the versions
		assertEquals(false, sat("multOne.als", "multLone.als", Analysis.SemDiff));
		assertEquals(true, sat("multLone.als", "multOne.als", Analysis.SemDiff));
		assertEquals(true, sat("oneA.als", "someA.als", Analysis.Equivalence));
		assertEquals(false, sat("someA.als", "oneA.als", Analysis.SemDiff));
	}
}
