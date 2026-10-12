package org.alloytools.alloy.diff;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

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


    private void selfMergeSigCount(Path f) {
        String fName = f.toString();
        Module v1 = CompUtil.parseEverything_fromFile(rep, null, fName);

        int sigNum = v1.getAllReachableUserDefinedSigs().size();

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v1);

        assertEquals(sigNum, sigs.size());
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

    
    @Test
    public void testMergeFieldCycle() throws Exception {
        String module1 = """
        sig A {
            f1 : set A,
            f2 : A - f1
        }
        """;
        String module2 = """
        sig A {
            f2 : set A,
            f1 : A - f2
        }        
        """;

        String pred = "some A";
        checkV2notV1(module1, module2, pred, true);
    }

    @Test
    public void testMergeFieldCycleComplexType() throws Exception {
        String module1 = """
        sig B extends A {}
        sig A {
            f1 : set B,
            f2 : A - f1
        }
        """;
        String module2 = """
        sig A {
            f2 : set A,
            f1 : A - f2
        }        
        """;

        String pred = "one A";
        checkV2notV1(module1, module2, pred, true);
    }

    /**
     * Tests that a sig-qualified function (fun Sig.name[...]) works when the
     * function is called from a fact. This exercises the FIXME in
     * replaceSigRefs(Func) and getExprVarToSig.
     */
    @Test
    public void testFunctionsWithSigRef() throws Exception {
        String module1 = """
        sig A {
            f : set A
        }
        fun A.reach[] : set A {
            this.^f
        }
        fact { all a: A | a not in a.reach }
        """;
        String module2 = """
        sig A {
            f : set A
        }
        fun A.reach[] : set A {
            this.^f
        }
        fact { all a: A | a not in a.reach }
        """;

        // Identical modules → diff should be unsatisfiable
        checkV2notV1(module1, module2, "", false);
    }

    /**
     * Tests sig-qualified function with abstract sig + subsigs.
     * The abstract sig with subsigs in both modules is NOT added to the merged
     * sigs map, so getExprVarToSig must handle this case.
     */
    @Test
    public void testFunctionsWithSigRefAbstract() throws Exception {
        String module1 = """
        abstract sig Base {}
        sig Sub1 extends Base {
            val : one Int
        }
        fun Base.getVal[] : Int {
            this.val
        }
        fact { all b: Base | b.getVal > 0 }
        """;
        String module2 = """
        abstract sig Base {}
        sig Sub1 extends Base {
            val : one Int
        }
        fun Base.getVal[] : Int {
            this.val
        }
        fact { all b: Base | b.getVal >= 0 }
        """;

        // v2 allows val=0, v1 does not → diff should be satisfiable
        checkV2notV1(module1, module2, "", true);
    }

    private static boolean solve(String module1, String module2, Analysis a, boolean withPred) {
        Module v1 = CompUtil.parseEverything_fromString(rep, module1);
        Module v2 = CompUtil.parseEverything_fromString(rep, module2);
        ModuleMerger merger = new ModuleMerger();
        Collection<Sig> mergedSigs = merger.mergeSigs(v1, v2);
        Command cmd = new CommandGenerator(merger).generateDiffCommand(v1, v2, 3, withPred, a);
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, mergedSigs, cmd, new A4Options());
        return ans.satisfiable();
    }

    private static boolean solve(String module1, String module2, Analysis a, int scope, boolean withPred) {
        Module v1 = CompUtil.parseEverything_fromString(rep, module1);
        Module v2 = CompUtil.parseEverything_fromString(rep, module2);
        ModuleMerger merger = new ModuleMerger();
        Collection<Sig> mergedSigs = merger.mergeSigs(v1, v2);
        Command cmd = new CommandGenerator(merger).generateDiffCommand(v1, v2, scope, withPred, a);
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, mergedSigs, cmd, new A4Options());
        return ans.satisfiable();
    }

    private static void check(String module1, String module2, Analysis a, boolean withPred, boolean expectSat) {
        assertEquals(expectSat, solve(module1, module2, a, withPred));
    }


    /** S in A must allow atoms of B extends A (merged sigs are flat). */
    @Test
    public void subsetSigContainsAtomsOfParentsSubSigs() {
        String m = """
                sig A {}
                sig B extends A {}
                sig S in A {}
                fact { some S & B }
                """;
        // the model has instances (plain Alloy: SAT)
        check(m, m, Analysis.CommonInst, false, true);
        check(m, m, Analysis.Equivalence, false, false);
    }

    /** same through a chain of SubsetSigs. */
    @Test
    public void subsetSigChainContainsAtomsOfParentsSubSigs() {
        String m = """
                sig A {}
                sig B extends A {}
                sig C in A {}
                sig D in C {}
                fact { some D & B }
                """;
        check(m, m, Analysis.CommonInst, false, true);
    }

    /** a SubsetSig unique to v2 must include the sub-sigs of its parent. */
    @Test
    public void uniqueSubsetSigOfV2ContainsAtomsOfParentsSubSigs() {
        String m1 = """
                sig A {}
                sig B extends A {}
                """;
        String m2 = """
                sig A {}
                sig B extends A {}
                sig S in A {}
                fact { some S & B }
                """;
        // every instance of m2 has some S, which m1 does not have
        check(m1, m2, Analysis.SemDiff, false, true);
    }

    /** a model must be equivalent to itself (tube.als pattern). */
    @Test
    public void selfEquivalenceWithSubsetSigOverAbstractParent() {
        String m = """
                abstract sig Station {}
                sig Line in Station {}
                one sig S1, S2, S3 extends Station {}
                """;
        check(m, m, Analysis.Equivalence, false, false);
    }

    /** "some sig A" is satisfied by atoms of B extends A. */
    @Test
    public void someParentSatisfiedBySubSigAtoms() {
        String m = """
                some sig A {}
                sig B extends A {}
                fact { no A - B }
                """;
        check(m, m, Analysis.CommonInst, false, true);
        check(m, m, Analysis.Equivalence, false, false);
    }

    /** "lone sig A" restricts A together with B extends A. */
    @Test
    public void loneParentRestrictsSubSigAtoms() {
        String m = """
                lone sig A {}
                sig B extends A {}
                fact { #A = 2 }
                """;
        // the model has no instance (plain Alloy: UNSAT)
        check(m, m, Analysis.CommonInst, false, false);
    }

    /** multiplicity of a parent that has sub-sigs in one version only. */
    @Test
    public void someParentWithSubSigsInOneVersionOnly() {
        String m1 = """
                some sig A {}
                """;
        String m2 = """
                some sig A {}
                sig B extends A {}
                fact { no A - B }
                """;
        // instances of m2 have B atoms, m1 has no B
        check(m1, m2, Analysis.SemDiff, false, true);
    }

    /**
     * abstract with sub-sigs in v1, abstract without sub-sigs in v2. v1 has
     * no instance (A has no atoms outside B), so there is no common instance.
     */
    @Test
    public void abstractWithAndWithoutChildren() {
        String m1 = """
                abstract sig A {}
                sig B extends A {}
                fact { some A - B }
                """;
        String m2 = """
                abstract sig A {}
                """;
        check(m1, m2, Analysis.CommonInst, false, false);
        // m1 has no instances, m2 has: not equivalent
        check(m1, m2, Analysis.Equivalence, false, true);
    }

    /**
     * "exactly 2 P" bounds P together with C extends P; it must not force C to
     * be empty. Needs withPred = true, otherwise the command scope is not used.
     */
    @Test
    public void exactScopeOnParentSig() {
        String m = """
                sig P {}
                sig C extends P {}
                fact { some C }
                run {} for exactly 2 P
                """;
        check(m, m, Analysis.CommonInst, true, true);
        check(m, m, Analysis.Equivalence, true, false);
    }

    /** util/ordering makes the ordered signature exact. */
    @Test
    public void orderedParentSigWithSubSig() {
        String m = """
                open util/ordering[P]
                sig P {}
                sig C extends P {}
                fact { some C and some P - C }
                run {} for 3
                """;
        check(m, m, Analysis.CommonInst, true, true);
    }

    /**
     * at scope 3 "#A <= 4" excludes nothing, so there is no difference. Before
     * the fix the literal 4 overflowed (bitwidth 3) and a spurious difference
     * (the empty instance) was reported.
     */
    @Test
    public void literalInFactDoesNotOverflow() {
        String m1 = """
                sig A {}
                fact { #A <= 4 }
                """;
        String m2 = """
                sig A {}
                """;
        check(m1, m2, Analysis.SemDiff, false, false);
        check(m1, m2, Analysis.Equivalence, false, false);
    }

    /** Alloy's default bitwidth 4 represents 4..7. */
    @Test
    public void defaultBitwidthIsAlloysDefault() {
        String m = """
                sig A { n: Int }
                fact { some A and all a: A | a.n > 3 }
                """;
        check(m, m, Analysis.CommonInst, false, true);
    }

    /**
     * the bitwidth of the command ("but 6 Int", range -32..31) is used. With
     * Alloy's default bitwidth 4 (max 7) or the old computed bitwidth 3 there is
     * no instance.
     */
    @Test
    public void bitwidthOfCommandIsUsed() {
        String m = """
                sig A { n: Int }
                fact { some A and all a: A | a.n > 7 and a.n < 20 }
                run {} for 3 but 6 Int
                """;
        check(m, m, Analysis.CommonInst, true, true);
    }

    /** binary field unique to v1 with an arrow multiplicity. */
    @Test
    public void uniqueBinaryFieldWithArrowMultiplicity() {
        String m1 = """
                sig A { f: B -> one C }
                sig B {}
                sig C {}
                """;
        String m2 = """
                sig A {}
                sig B {}
                sig C {}
                fact { some A and some B }
                """;
        // instances of m2 with A and B atoms have no f, m1 requires f to be total
        check(m1, m2, Analysis.SemDiff, false, true);
    }

    /** binary field of a SubsetSig with an arrow multiplicity. */
    @Test
    public void subsetSigBinaryFieldWithArrowMultiplicity() {
        String m = """
                sig B {}
                sig A {}
                sig S in A { f: B -> one B }
                fact { some A - S and some B }
                """;
        check(m, m, Analysis.CommonInst, false, true);
        check(m, m, Analysis.Equivalence, false, false);
    }

    /**
     * opposite field orders create a field cycle in the merge. The placeholder
     * field must allow sets (not "one") and atoms of B extends A.
     */
    @Test
    public void fieldCyclePlaceholderAllowsSetsAndSubSigAtoms() {
        String m1 = """
                sig A { f: set A, g: set f }
                sig B extends A {}
                fact { some a: A | some a.f & B }
                """;
        String m2 = """
                sig A { g: set A, f: set g }
                sig B extends A {}
                fact { some a: A | some a.f & B }
                """;
        check(m1, m2, Analysis.CommonInst, false, true);
    }

    /** the placeholder of a mutable field must be mutable. */
    @Test
    public void fieldCyclePlaceholderKeepsVar() {
        String m1 = """
                sig A { var f: set A, var g: set f }
                fact { eventually f != f' }
                """;
        String m2 = """
                sig A { var g: set A, var f: set g }
                fact { eventually f != f' }
                """;
        check(m1, m2, Analysis.CommonInst, false, true);
    }

    /**
     * in m1 field f is static, so with no S in the first state f is
     * empty forever. The m2 trace in which S.f becomes non-empty later is not a
     * trace of m1.
     */
    @Test
    public void staticFieldOfVarSigIsFramedAsAWhole() {
        String m1 = """
                sig B {}
                var sig S { f: set B }
                """;
        String m2 = """
                sig B {}
                var sig S { var f: set B }
                fact { no S and eventually some S.f }
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, 3, false));
    }

    /**
     * Alloy enforces "f: one B" of a static field of a var sig
     * in every state, also for atoms that join S later. In m1 (no S at first, so f
     * is empty forever) a later S atom violates "one B"; m2 allows it.
     */
    @Test
    public void staticFieldDeclarationOfVarSigHoldsInAllStates() {
        String m1 = """
                sig B {}
                var sig S { f: one B }
                """;
        String m2 = """
                sig B {}
                var sig S { var f: lone B }
                fact { some B and no S and eventually some S }
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, 3, false));
    }

    /** the fix must not exclude traces: a static field is also a var field. */
    @Test
    public void staticFieldTracesAreVarFieldTraces() {
        String m1 = """
                sig B {}
                var sig S { var f: one B }
                """;
        String m2 = """
                sig B {}
                var sig S { f: one B }
                """;
        assertEquals(false, solve(m1, m2, Analysis.SemDiff, 3, false));
    }

    /**
     * "for 2 S" bounds the atoms that S uses over the whole trace. m2 uses 3
     * distinct atoms (after an empty first state), which m1 cannot.
     */
    @Test
    public void scopeOfVarSigBoundsAllStates() {
        String m1 = """
                var sig S {}
                run {} for 2 S
                """;
        String m2 = """
                var sig S {}
                fact { no S and eventually #S = 3 }
                run {} for 3 S
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, -1, true));
    }

    /** same for a var signature hierarchy (bound on parent plus children). */
    @Test
    public void scopeOfVarSigHierarchyBoundsAllStates() {
        String m1 = """
                var sig P {}
                var sig C extends P {}
                run {} for 2 P
                """;
        String m2 = """
                var sig P {}
                var sig C extends P {}
                fact { no P and eventually (one C and after (one C and C' != C and after (one P - C))) }
                run {} for 3 P
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, -1, true));
    }

    /** the larger scope includes all traces of the smaller one. */
    @Test
    public void smallerVarScopeIsIncluded() {
        String m1 = """
                var sig S {}
                run {} for 3 S
                """;
        String m2 = """
                var sig S {}
                run {} for 2 S
                """;
        assertEquals(false, solve(m1, m2, Analysis.SemDiff, -1, true));
    }

    /**
     * scope -1 (used by the GUI) compares with the scopes of the commands. At
     * scope 5, m2 has an instance with 5 atoms that m1 excludes.
     */
    @Test
    public void scopeMinusOneUsesCommandScopes() {
        String m1 = """
                sig A {}
                fact { #A <= 4 }
                run {} for 5
                """;
        String m2 = """
                sig A {}
                run {} for 5
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, -1, true));
        // an explicit maximum scope still caps the comparison
        assertEquals(false, solve(m1, m2, Analysis.SemDiff, 3, true));
    }

    /** different command scopes are compared as given. */
    @Test
    public void largerCommandScopeAddsInstances() {
        String m1 = """
                sig A {}
                run {} for 3
                """;
        String m2 = """
                sig A {}
                run {} for 4
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, -1, true));
        assertEquals(false, solve(m2, m1, Analysis.SemDiff, -1, true));
    }

    /** an exact scope above 3 is respected. */
    @Test
    public void exactScopeAboveThree() {
        String m = """
                sig A {}
                fact { #A = 4 }
                run {} for exactly 4 A
                """;
        assertEquals(true, solve(m, m, Analysis.CommonInst, -1, true));
    }

    /**
     * a signature fact of a var sig holds in every state (as in Alloy). The
     * model has no instance: "no B" must also hold once S has atoms.
     */
    @Test
    public void sigFactOfVarSigHoldsInAllStates() {
        String m = """
                sig B {}
                var sig S {} { no B }
                fact { some B and no S and eventually some S }
                """;
        assertEquals(false, solve(m, m, Analysis.CommonInst, 3, false));
    }

    /** a sig fact is temporal if it calls a predicate on mutable state. */
    @Test
    public void sigFactCallingTemporalPredicateHoldsInAllStates() {
        String m = """
                sig B {}
                var sig X {}
                pred q { no X }
                sig S {} { q }
                fact { some S and no X and eventually some X }
                """;
        assertEquals(false, solve(m, m, Analysis.CommonInst, 3, false));
    }

    /** the m2 trace violates the sig fact of m1 in a later state. */
    @Test
    public void sigFactOfVarSigDifference() {
        String m1 = """
                sig B {}
                var sig S {} { no B }
                """;
        String m2 = """
                sig B {}
                var sig S {}
                fact { some B and no S and eventually some S }
                """;
        assertEquals(true, solve(m1, m2, Analysis.SemDiff, 3, false));
    }

}
