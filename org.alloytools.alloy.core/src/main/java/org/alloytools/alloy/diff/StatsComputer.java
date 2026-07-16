package org.alloytools.alloy.diff;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

/**
 * CLI/API experiment runner for collecting structural statistics (#sigs, #fields, #facts/#funcs) across models.
 * Usage: java -cp org.alloytools.alloy.dist.jar org.alloytools.alloy.diff.StatsComputer [folder1 folder2 ...]
 */
public class StatsComputer {
	static String[] defaultFolders = new String[] { "misc", "models-master", "../models-master", "iAlloy-dataset-master", "../iAlloy-dataset-master",
			"platinum-experiment-data", "../platinum-experiment-data/" };

	public static void main(String[] args) throws IOException {
		String[] folders = args.length > 0 ? args : defaultFolders;
		for (String folder : folders) {
			Path p = Paths.get(folder);
			if (!Files.exists(p)) continue;
			Files
					.find(p, Integer.MAX_VALUE,
							(filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als"))
					.forEach(f -> {
						try {
							writeStats(f);
						} catch (Exception e) {

						}
					});
		}
	}

	private static Object writeStats(Path f) throws IOException {
		CompModule m = CompUtil.parseEverything_fromFile(ModuleDiff.rep, null, f.toString());
		String report = f.toString() + "; " + 
				Files.readAllLines(f).size() + "; " + 
				m.getAllReachableUserDefinedSigs().size() + "; " + 
				countFields(m.getAllReachableUserDefinedSigs()) + "; " +
				countFactFunPref(m) + "\r\n";
	
		Files.writeString(Paths.get("stats.csv"), report, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
		System.out.println("Recorded stats for " + f.getFileName());
		return null;
	}

	private static int countFactFunPref(CompModule m) {
		int count = 0;
		for (Module rm : m.getAllReachableModules()) {
			String path = rm.path();
			String name = rm.getModuleName();
			if (!"util/integer".equals(name) && (path == null || !path.contains("util/integer"))) {
				count += rm.getAllFunc().size();
				count += rm.getAllFacts().size();
			}
		}
		for (Sig s : m.getAllReachableUserDefinedSigs()) {
			count += s.getFacts().size();
		}
		
		return count;
	}

	private static int countFields(ConstList<Sig> sigs) {
		int count = 0; 

		for (Sig s: sigs) {
			count += s.getFields().size();
		}
		return count;
	}
}
