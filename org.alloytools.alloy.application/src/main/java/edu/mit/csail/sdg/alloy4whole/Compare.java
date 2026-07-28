package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.IOException;

import org.alloytools.alloy.diff.Analysis;
import org.alloytools.alloy.diff.ModuleDiff;

import edu.mit.csail.sdg.alloy4.Computer;
import edu.mit.csail.sdg.alloy4.OurDialog;
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

	public static void CompareModules(String leftFile, String rightFile, int leftCmdIndex, int rightCmdIndex, String analysis, SwingLogPanel log) {
		if (log != null) {
			log.clearError();
			log.logDivider();

			log.logBold("Comparing: " + new File(leftFile).getName() + " with " + new File(rightFile).getName());
		}
		switch (analysis) {
		case "Semantic Diff":
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.SemDiff);
			break;
		case "Common Instances":
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.CommonInst);
			break;
		case "Equivalence":
			ans = ModuleDiff.diff(rightFile, leftFile, rightCmdIndex, leftCmdIndex, -1, true, Analysis.Equivalence);
			if (ans.satisfiable()) {
				if (log != null) {
					log.logRed("\nNot equivalent.\n Counter-example found. Visualizer opened.\n");
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
			break;
		}

		if (ans.satisfiable()) {
			if (log != null) {
				log.log("\nInstance Found. Visualizer opened.\n");
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
							writeSolutionXML(Compare.ans, ALLOY_EXAMPLE_OUTPUT_XML);
							viz.loadXML(ALLOY_EXAMPLE_OUTPUT_XML, true);
							if (log != null) {
								// log.log("Next solution displayed.\r\n");
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
