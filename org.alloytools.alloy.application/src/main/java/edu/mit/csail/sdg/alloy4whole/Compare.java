package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.alloytools.alloy.diff.Analysis;
import org.alloytools.alloy.diff.ConstraintInfo;
import org.alloytools.alloy.diff.ConstraintOrigin;
import org.alloytools.alloy.diff.DiffExplanation;
import org.alloytools.alloy.diff.ModuleDiff;
import org.alloytools.alloy.diff.ModuleMerger;

import edu.mit.csail.sdg.alloy4.Computer;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.translator.A4Solution;

public class Compare {

	static {
		try {
			ALLOY_EXAMPLE_OUTPUT_XML = File.createTempFile("alloyInst", ".xml").getAbsolutePath();
		} catch (IOException e) {
			ALLOY_EXAMPLE_OUTPUT_XML = "alloy_example_output.xml";
		}
	}

	private static String ALLOY_EXAMPLE_OUTPUT_XML;
	public static A4Solution ans;
	public static VizGUI viz;
	/**
	 * The merger of the comparison currently being shown. Captured when the
	 * comparison runs rather than read from ModuleDiff at logging time, so that
	 * enumerating instances of an older comparison cannot pick up the constraints
	 * of a newer one.
	 */
	private static ModuleMerger merger;
	/** The analysis the current comparison was started with. */
	private static Analysis lastAnalysis;
	/** 1-based index of the witness currently shown, for labelling the log. */
	private static int instanceIndex;
	/** The explanation of the witness currently shown, if any. */
	private static DiffExplanation.Explanation lastExplanation;

	public static void CompareModules(String leftFile, String rightFile, int leftCmdIndex, int rightCmdIndex, String analysis, SwingLogPanel log) {
		if (log != null) {
			log.clearError();
			log.logDivider();

			log.logBold("Comparing: " + new File(leftFile).getName() + " with " + new File(rightFile).getName());
		}
		merger = null;
		lastExplanation = null;
		instanceIndex = 1;
		switch (analysis) {
		case "Semantic Diff":
			// ModuleDiff.diff(v1=rightFile, v2=leftFile) computes c2.and(c1.not())
			// i.e. instances of leftFile that are NOT instances of rightFile
			lastAnalysis = Analysis.SemDiff;
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.SemDiff);
			merger = ModuleDiff.getLastMerger();
			break;
		case "Common Instances":
			lastAnalysis = Analysis.CommonInst;
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.CommonInst);
			merger = ModuleDiff.getLastMerger();
			break;
		case "Equivalence":
			lastAnalysis = Analysis.Equivalence;
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.Equivalence);
			merger = ModuleDiff.getLastMerger();
			if (ans.satisfiable()) {
				if (log != null) {
					log.logRed("\nNot equivalent.\n Counter-example found. Visualizer opened.\n");
					logExplanation(log);
				}
			} else {
				if (log != null) {
					log.log("\nModels are equivalent.\n");
				}
			}
			log.flush();
			showViz(log);
			return;
		default:
			lastAnalysis = null;
			break;
		}

		if (ans.satisfiable()) {
			if (log != null) {
				log.log("\nInstance Found. Visualizer opened.\n");
				logExplanation(log);
			} else {
				System.out.println(ans);
			}
		} else {
			if (log != null) {
				log.logRed(ans + "\n");
			} else {
				System.out.println(ans);
			}
		}

		log.flush();
		showViz(log);
	}

	/**
	 * Logs the constraints violated by the witness currently in {@link #ans} as
	 * clickable links. Clicking a link highlights the corresponding conjunct in
	 * the editor.
	 *
	 * <p>
	 * An explanation only holds for the witness it was computed from: the diff
	 * command merely asserts that <em>some</em> conjunct of the rejecting side is
	 * false, and the next instance may falsify a different one. It is therefore
	 * recomputed for every witness, labelled with the instance number, and any
	 * highlighting left over from the previous instance is removed.
	 *
	 * <p>
	 * For SemDiff (c2 &and; &not;c1): the witness satisfies c2 but violates c1.
	 * c1 = rightFile constraints (v1), c2 = leftFile constraints (v2). Violated
	 * c1 constraints explain WHY the witness is not valid in rightFile.
	 *
	 * <p>
	 * For Equivalence (&not;(c1 &harr; c2)): the witness satisfies one side but
	 * not the other, so violations from both sides are reported.
	 */
	private static void logExplanation(SwingLogPanel log) {
		lastExplanation = null;
		if (merger == null || lastAnalysis == null || ans == null || !ans.satisfiable()) {
			return;
		}
		if (lastAnalysis == Analysis.CommonInst) {
			// both sides are satisfied, there is nothing to explain
			return;
		}

		// the previous instance's highlighting no longer explains anything
		log.clearShading();

		DiffExplanation.Explanation explanation = DiffExplanation.explain(ans, merger, lastAnalysis);
		lastExplanation = explanation;

		if (lastAnalysis == Analysis.SemDiff) {
			logViolatedConstraints(log, explanation.violatedC1(),
					"Instance #" + instanceIndex + " — violated constraints (why this instance is rejected):");
		} else {
			logViolatedConstraints(log, explanation.violatedC1(),
					"Instance #" + instanceIndex + " — violated in right model:");
			logViolatedConstraints(log, explanation.violatedC2(),
					"Instance #" + instanceIndex + " — violated in left model:");
		}

		if (!explanation.isComplete()) {
			log.logRed("  No violated constraint found for this instance — the explanation is incomplete.\n");
		}
	}

	/**
	 * Returns the explanation of the witness currently shown, or null if there is
	 * none. The caller should check {@link DiffExplanation.Explanation#isFor} to
	 * make sure it still refers to the witness of interest.
	 */
	public static DiffExplanation.Explanation getLastExplanation() {
		return lastExplanation;
	}

	/**
	 * Outputs a list of violated constraints as clickable links.
	 */
	private static void logViolatedConstraints(SwingLogPanel log, List<ConstraintInfo> violated, String header) {
		if (violated.isEmpty()) return;

		log.logBold("\n" + header + "\n");
		for (ConstraintInfo ci : violated) {
			Pos p = ci.pos();
			String originLabel = formatOrigin(ci.origin());
			int state = DiffExplanation.firstViolatingState(ans, ci);
			String when = state < 0 ? "" : " [first fails in state " + state + "]";
			if (ci.hasSourcePos()) {
				String snippet = DiffExplanation.sourceText(p, ModuleDiff.sources);
				String linkText = "  " + originLabel + " — " + new File(p.filename).getName() + " (line " + p.y + ")"
						+ (snippet.isEmpty() ? "" : ":  " + abbreviate(snippet)) + when + "\n";
				String linkDest = "POS: " + p.x + " " + p.y + " " + p.x2 + " " + p.y2 + " " + p.filename;
				log.logLink(linkText, linkDest);
			} else {
				log.log("  " + originLabel + " (synthesized, no source position)\n");
			}
		}
	}

	private static String abbreviate(String s) {
		return s.length() <= 120 ? s : s.substring(0, 117) + "...";
	}

	/**
	 * Formats a ConstraintOrigin enum value into a human-readable label.
	 */
	private static String formatOrigin(ConstraintOrigin origin) {
		switch (origin) {
		case SIG_ATTRIBUTE:      return "Sig attribute";
		case SIG_HIERARCHY:      return "Sig hierarchy";
		case FIELD_MULTIPLICITY: return "Field multiplicity";
		case FIELD_FRAME:        return "Field frame condition";
		case FIELD_DISJOINT:     return "Disjoint fields";
		case SIG_FACT:           return "Sig fact";
		case CLOSED_WORLD:       return "Closed-world assumption";
		case FACT:               return "Fact";
		case COMMAND_PREDICATE:  return "Command predicate";
		case SCOPE_BOUND:        return "Scope bound";
		default:                 return origin.name();
		}
	}

	private static void showViz(SwingLogPanel log) {
		// If satisfiable...
		if (ans.satisfiable()) {
			// You can query "ans" to find out the values of each set or
			// type.
			// This can be useful for debugging.
			//
			// You can also write the outcome to an XML file
			try {
				writeSolutionXML(ans, ALLOY_EXAMPLE_OUTPUT_XML);
			} catch (Exception ex) {
				if (log != null) log.logRed(ex.getMessage() + "\r\n");
			}
			//

			Computer enumerator = new Computer() {
				@Override
				public String compute(Object input) {
					final String[] arg = (String[]) input;
					int index = -3;
					try {
						index = Integer.parseInt(arg[1]);
					} catch (NumberFormatException e) {
						index = -3;
					}
					try {
						A4Solution nextAns = Compare.ans.fork(index);
						if (nextAns.satisfiable()) {
							Compare.ans = nextAns;
							Compare.instanceIndex++;
							writeSolutionXML(Compare.ans, ALLOY_EXAMPLE_OUTPUT_XML);
							viz.loadXML(ALLOY_EXAMPLE_OUTPUT_XML, true);
							if (log != null) {
								log.logDivider();
								log.log("Next instance found.\n");
								logExplanation(log);
								log.flush();
							}
						} else {
							if (log != null) {
								log.log("No more solutions.\r\n");
								log.flush();
							}
							OurDialog.alert(viz.getFrame(), "There are no more satisfying instances.\n\nNote: due to symmetry breaking and other optimizations,\nsome equivalent solutions may have been omitted.");
						}
					} catch (Throwable ex) {
						if (log != null) {
							log.logRed(ex.getMessage() + "\r\n");
							log.flush();
						}
						OurDialog.alert(viz.getFrame(), ex.getMessage());
					}
					return arg[0];
				}
			};

			// You can then visualize the XML file by calling this:
			viz = new VizGUI(false, ALLOY_EXAMPLE_OUTPUT_XML, null, enumerator, SimpleGUI.getEvaluator(), 2);
		}
	}

	private static void writeSolutionXML(A4Solution sol, String filename) throws Exception {
		sol.writeXML(filename, null, ModuleDiff.sources);
	}
}
