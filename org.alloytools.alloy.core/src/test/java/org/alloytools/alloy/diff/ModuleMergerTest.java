package org.alloytools.alloy.diff;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class ModuleMergerTest {

    public static A4Reporter rep;

    @BeforeClass
    public static void setup() {
        rep = new A4Reporter() {

            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };
    }

    /**
     * tests if two modules signature counts have changed when they are not supposed
     * to change Ex. If both modules have signature names that do not match then,
     * then the merged module should have all signatures
     */
    @Test
    public void testSignatureCountV1() {

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/testSignatureCountv1.als");
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/testSignatureCountv2.als");

        int v1SigsCount = v1.getAllReachableUserDefinedSigs().size();
        int v2SigsCount = v2.getAllReachableUserDefinedSigs().size();

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        assertEquals(v1SigsCount + v2SigsCount, sigs.size());
    }

    /**
     * tests if two modules signature counts have changed as needed Ex. If module 1
     * has 2 signatures and module 2 has 2 signatures, and 1 signature name is
     * common between both, then the merged module should have 3 signatures
     */
    @Test
    public void testSignatureCountV2() {

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/v2testSignatureCountv1.als");
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/v2testSignatureCountv2.als");

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        assertEquals(3, sigs.size());
    }

    /**
     * tests if field names Ex. TODO
     */
    @Test
    public void testFields() {

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/fieldTest1v1.als");
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/fieldTest1v2.als");

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        assertEquals(1, getFieldCount(sigs));
    }

    /**
     * tests if field names Ex. TODO
     */
    @Test
    public void testFields2() {

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/fieldTest2v1.als");
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/multiplicities/tests/fieldTest2v2.als");

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        assertEquals(3, getFieldCount(sigs));
    }

    private int getFieldCount(Collection<Sig> sigs) {
        int fieldCount = 0;
        for (Sig sig : sigs) {
            fieldCount = fieldCount + sig.getFields().size();
        }
        return fieldCount;
    }

    /**
     * tests if two modules signature counts have changed when they are not supposed
     * to change Ex. If both modules have signature names that do not match then,
     * then the merged module should have all signatures
     */
    @Test
    public void selfMergeSigCountTest() throws Exception {
        Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(f -> selfMergeSigCount(f));
    }

    private void selfMergeSigCount(Path f) {
        String fName = f.toString();
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);

        int sigNum = v1.getAllReachableUserDefinedSigs().size();

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v1);

        assertEquals(sigNum, sigs.size());
    }

    @Test
    public void selfMergeWithEmptySigCountTest() throws Exception {
        Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(f -> selfMergeWithEmptySigCount(f));
    }

    public void selfMergeWithEmptySigCount(Path f) {
        String fName = f.toString();
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);
        Module empty = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/empty.als");

        int sigNum = v1.getAllReachableUserDefinedSigs().size();

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, empty);

        assertEquals(sigNum, sigs.size());

        sigs = m.mergeSigs(empty, v1);

        assertEquals(sigNum, sigs.size());

    }

    @Test
    public void selfMergeWithOneSigCountTest() throws Exception {
        Files.find(Paths.get("src/test/resources/misc/string/string2.als"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(f -> selfMergeWithOneSigCount(f));
    }

    public void selfMergeWithOneSigCount(Path f) {
        String fName = f.toString();
        //		System.out.println(fName);
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);
        Module one = CompUtil.parseEverything_fromFile(rep, null, "src/test/resources/misc/one.als");

        if (fName.contains("src/test/resources/misc/one.als") || fName.contains("src/test/resources/misc/one.als")) {
            return;
        }

        int sigNum = v1.getAllReachableUserDefinedSigs().size();

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, one);

        assertEquals(sigNum + 1, sigs.size());

        sigs = m.mergeSigs(one, v1);

        assertEquals(sigNum + 1, sigs.size());
    }

    @Test
    public void mergeSigNamesTest() throws Exception {
        Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(p1 -> {
            try {
                Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(p2 -> mergeSigNames(p1, p2));
            } catch (IOException e) {
                e.printStackTrace();
                fail();
            }
        });
    }

    private void mergeSigNames(Path p1, Path p2) {
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, p1.toString());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, p2.toString());

        Set<String> allNames = getSigNames(v1.getAllReachableUserDefinedSigs());
        allNames.addAll(getSigNames(v2.getAllReachableUserDefinedSigs()));

        ModuleMerger m = new ModuleMerger();
        Set<String> mergedNames = getSigNames(m.mergeSigs(v1, v2));
        assertEquals(allNames, mergedNames);
    }

    private Set<String> getSigNames(Iterable<Sig> allSigs) {
        Set<String> names = new HashSet<String>();
        for (Sig s : allSigs) {
            names.add(s.label);
        }
        return names;
    }


    @Test
    public void mergeFieldNamesTest() throws Exception {
        Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(p1 -> {
            try {
                Files.find(Paths.get("src/test/resources/misc"), Integer.MAX_VALUE, (filePath, fileAttr) -> fileAttr.isRegularFile() && filePath.toString().endsWith(".als")).forEach(p2 -> mergeFieldNames(p1, p2));
            } catch (IOException e) {
                e.printStackTrace();
                fail();
            }
        });
    }

    private void mergeFieldNames(Path p1, Path p2) {
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, p1.toString());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, p2.toString());

        List<Sig> allSigsv1 = v1.getAllReachableUserDefinedSigs();
        List<Sig> allSigsv2 = v2.getAllReachableUserDefinedSigs();

        Set<Sig> unique1 = new HashSet<Sig>();
        unique1.addAll(allSigsv1);
        Set<Sig> unique2 = new HashSet<Sig>();
        unique2.addAll(allSigsv2);

        ModuleMerger m = new ModuleMerger();
        Iterable<Sig> mergedSigs = null;
        try {
            mergedSigs = m.mergeSigs(v1, v2);
        } catch (Exception e) {
            if (e.getMessage() != null && e.getMessage().contains("Ordering")) {
                return;
            } else {
                throw e;
            }
        }

        // not unique
        for (Sig s : allSigsv1) {
            for (Sig s2 : allSigsv2) {
                if (s.label.equals(s2.label)) {
                    int noOfFieldsinS1 = s.getFields().size();
                    int noOfFieldsinS2 = s2.getFields().size();

                    int fieldCount = getFieldCount(s.label, mergedSigs);

                    // min no of merged fields should be the max no of fields in either module
                    assertTrue(fieldCount >= Math.max(noOfFieldsinS1, noOfFieldsinS2));
                    // max no of merged fields needs to be the sum of fields.
                    assertTrue(fieldCount <= (noOfFieldsinS1 + noOfFieldsinS2));

                    unique1.remove(s);
                    unique2.remove(s2);
                }
            }
        }

        // unique
        {
            // no of fields should be the same as in the original module
            for (Sig s : unique1) {
                //				System.out.println(s.label + " " + p1);
                assertEquals(s.getFields().size(), getFieldCount(s.label, mergedSigs));
            }
            for (Sig s2 : unique2) {
                //				System.out.println(s2.label + " " + p2);
                assertEquals(s2.getFields().size(), getFieldCount(s2.label, mergedSigs));
            }
        }

    }

    private int getFieldCount(String sigName, Iterable<Sig> mergedSigs) {
        int fieldCount = 0;
        for (Sig s : mergedSigs) {
            if (s.label.equals(sigName)) {
                return s.getFields().size();
            }
        }
        return fieldCount;
    }


    @Test
    public void testSubsetSigExact() throws Exception {
        // Defining C exactly as A in module1 and exactly as B in module2
        String module1 = """
        sig A, B {}
        sig C = A {}
        """;
        String module2 = """
        sig A, B {}
        sig C = B {}
        """;
        
        String pred = "some A & B";
        checkV2notV1(module1, module2, pred, false);
        checkV2notV1(module2, module1, pred, false);
        pred = "some C";
        checkV2notV1(module1, module2, pred, true);
    }

    @Test
    public void testSubsetSigMultipleParents() throws Exception {
        String module1 = """
        sig A, B, D {}
        sig C in A + B {}
        """;
        String module2 = """
        sig A, B, D {}
        sig C in A + D {}
        """;
        String pred = "some C & A";
        checkV2notV1(module1, module2, pred, true);
        checkV2notV1(module2, module1, pred, true);
    }

    @Test
    public void testSubsetSigMultipleIndirecParents() throws Exception {
        String module1 = """
        sig A, B {}
        sig D extends B {}
        sig C in A + B {}
        """;
        String module2 = """
        sig A, B, D {}
        sig C in A + D {}
        """;

        String pred = "some C & B";
        checkV2notV1(module1, module2, pred, false);
        checkV2notV1(module2, module1, pred, true);
    }

    @Test
    public void testSubsetSigHierarchyRestore() throws Exception {
        String module1 = """
        sig A, B {}
        sig C in A {}
        sig D in C + B {}
        """;
        String module2 = """
        sig A, B {}
        sig C in A + B {}
        """;

        String pred = "some C & B";
        checkV2notV1(module1, module2, pred, true);
        checkV2notV1(module2, module1, pred, false);

        pred = "some D";
        checkV2notV1(module2, module1, pred, true);
    }

    public void checkV2notV1(String module1, String module2, String pred, boolean satisfiable) {
        Module v1 = CompUtil.parseEverything_fromString(rep, module1);

        String v2withPred = module2 + "fact {" + pred + "}";
        Module v2 = CompUtil.parseEverything_fromString(rep, v2withPred);

        ModuleMerger merger = new ModuleMerger();
        Collection<Sig> mergedSigs = merger.mergeSigs(v1, v2);

        CommandGenerator cg = new CommandGenerator(merger);
        Command diffCommand = cg.generateDiffCommand(v1, v2, 3, false, Analysis.SemDiff);
		//Command diffCommand = new Command(false, 3, 4, 4, merger.c2.and(merger.c1.not()));

		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, mergedSigs, diffCommand, new A4Options());
    
        assertEquals(satisfiable, ans.satisfiable());
    }

    public void checkEquivalent(String module1, String module2, String pred, boolean satisfiable){
        Module v1 = CompUtil.parseEverything_fromString(rep, module1);

        String v2withPred = module2 + "fact {" + pred + "}";
        Module v2 = CompUtil.parseEverything_fromString(rep, v2withPred);

        ModuleMerger merger = new ModuleMerger();
        Collection<Sig> mergedSigs = merger.mergeSigs(v1, v2);

        CommandGenerator cg = new CommandGenerator(merger);
        Command diffCommand = cg.generateDiffCommand(v1, v2, 3, false, Analysis.Equivalence);
		//Command diffCommand = new Command(false, 3, 4, 4, merger.c2.and(merger.c1.not()));

		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, mergedSigs, diffCommand, new A4Options());
    
        assertEquals(satisfiable, ans.satisfiable());
    }
}
