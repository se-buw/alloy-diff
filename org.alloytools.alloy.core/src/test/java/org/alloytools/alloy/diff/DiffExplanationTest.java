package org.alloytools.alloy.diff;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class DiffExplanationTest {

    private static A4Reporter rep = new A4Reporter();

    @Test
    public void testMultiplicityViolation() throws Exception {
        // v1: f is "one B" (exactly one), v2: f is "lone B" (zero or one)
        // SemDiff = c2.and(c1.not()) = instances of v2 that violate v1
        // Witness: an A with zero B's — satisfies "lone" but violates "one"
        File f1 = createTempFile("v1.als", "sig B {}\nsig A { f: one B }");
        File f2 = createTempFile("v2.als", "sig B {}\nsig A { f: lone B }");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        CommandGenerator cg = new CommandGenerator(m);
        Command diffCommand = cg.generateDiffCommand(v1, v2, -1, -1, 3, true, Analysis.SemDiff);

        A4Options opt = new A4Options();
        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, opt);

        assertTrue("Should be satisfiable", sol.satisfiable());

        List<ConstraintInfo> violated = DiffExplanation.getViolatedConstraints(sol, m.getC1Constraints());
        assertTrue("There should be violated constraints", violated.size() > 0);

        boolean hasFieldMult = violated.stream().anyMatch(c -> c.origin() == ConstraintOrigin.FIELD_MULTIPLICITY);
        assertTrue("Should have a violated FIELD_MULTIPLICITY constraint", hasFieldMult);
    }

    @Test
    public void testFactViolation() throws Exception {
        // v1 has a fact "all a: A | some a.f", v2 does not
        // SemDiff should find an instance where f is empty for some A (violating v1's fact)
        File f1 = createTempFile("v1.als", "sig B {}\nsig A { f: set B }\nfact { all a: A | some a.f }");
        File f2 = createTempFile("v2.als", "sig B {}\nsig A { f: set B }");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        CommandGenerator cg = new CommandGenerator(m);
        Command diffCommand = cg.generateDiffCommand(v1, v2, -1, -1, 3, true, Analysis.SemDiff);

        A4Options opt = new A4Options();
        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, opt);

        assertTrue("Should be satisfiable (v2 allows empty f)", sol.satisfiable());

        List<ConstraintInfo> violated = DiffExplanation.getViolatedConstraints(sol, m.getC1Constraints());
        assertTrue("There should be violated constraints", violated.size() > 0);

        // The violated constraint should include the FACT origin (the global fact from v1)
        boolean hasFact = violated.stream().anyMatch(c -> c.origin() == ConstraintOrigin.FACT);
        assertTrue("Should have a violated FACT constraint", hasFact);
    }

    @Test
    public void testConstraintOriginsAreTracked() throws Exception {
        // Verify that after merge + command generation, constraint lists are non-empty
        File f1 = createTempFile("v1.als", "sig A {}");
        File f2 = createTempFile("v2.als", "sig A {}\nsig B extends A {}");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        // After mergeSigs, at least c1 should have a closed-world constraint for B
        assertTrue("c1Constraints should have entries (closed-world for B)", m.getC1Constraints().size() > 0);

        // After generateDiffCommand, facts and scope bounds get added too
        CommandGenerator cg = new CommandGenerator(m);
        cg.generateDiffCommand(v1, v2, -1, -1, 3, true, Analysis.SemDiff);

        // Now both sides should have constraints (at minimum, the FACT entries)
        boolean hasC1 = m.getC1Constraints().size() > 0;
        boolean hasC2 = m.getC2Constraints().size() > 0;
        assertTrue("Both constraint lists should have entries after full command generation", hasC1 && hasC2);
    }

    /**
     * Alloy wraps a fact body in NOOP nodes whose position spans the whole
     * "fact {...}" declaration, and flattening a conjunction keeps those
     * wrappers. The tracked position must look through them so that only the
     * offending conjunct is highlighted, not the entire fact (and not the
     * following command, which the position of the enclosing AND spans).
     */
    @Test
    public void testViolatedPositionIsTheConjunctNotTheWholeFact() throws Exception {
        // line 1: sig Node ...
        // line 3: fact {
        // line 4: all n: Node | one n.edges <- the only conjunct that can differ
        // line 5: }
        // line 7: run {}
        String v1Src = "sig Node { edges: set Node }\n" //
                + "\n" //
                + "fact {\n" //
                + "  all n: Node | one n.edges\n" //
                + "}\n" //
                + "\n" //
                + "run {}\n";
        String v2Src = v1Src.replace("one n.edges", "lone n.edges");

        File f1 = createTempFile("v1.als", v1Src);
        File f2 = createTempFile("v2.als", v2Src);

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);

        CommandGenerator cg = new CommandGenerator(m);
        // command index 0 => the "withPred" path, where Command.formula is
        // "globalFacts and predicateBody"
        Command diffCommand = cg.generateDiffCommand(v1, v2, 0, 0, 3, true, Analysis.SemDiff);

        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, new A4Options());
        assertTrue("Should be satisfiable (v2 relaxes 'one' to 'lone')", sol.satisfiable());

        List<ConstraintInfo> violated = DiffExplanation.getViolatedConstraints(sol, m.getC1Constraints());
        ConstraintInfo fact = violated.stream().filter(c -> c.origin() == ConstraintOrigin.FACT).findFirst()
                .orElse(null);
        // the conjunct comes from a "fact", not from the run command, even though
        // Command.formula bundles the two together
        assertNotNull("The violated global fact should be reported with origin FACT", fact);

        Pos p = fact.pos();
        assertTrue("The position should be usable for highlighting", fact.hasSourcePos());
        assertEquals("Highlight should start on the line of the conjunct, not on 'fact {'", 4, p.y);
        assertEquals("Highlight should end on the line of the conjunct, not on '}' or 'run'", 4, p.y2);
        assertEquals("Highlight should start at the conjunct", 3, p.x);

        Map<String,String> sources = new LinkedHashMap<>();
        sources.put(p.filename, v1Src);
        assertEquals("all n: Node | one n.edges", DiffExplanation.sourceText(p, sources));
    }

    /**
     * Facts and the command predicate end up in the same Command.formula; they
     * must still be distinguishable in the explanation.
     */
    @Test
    public void testFactAndCommandPredicateAreLabelledSeparately() throws Exception {
        String v1Src = "sig Node { edges: set Node }\n" //
                + "fact { all n: Node | one n.edges }\n" //
                + "pred p { some Node }\n" //
                + "run p for 4 Node\n";
        // the exact scope in v2 makes the generator emit an explicit scope bound
        String v2Src = v1Src.replace("one n.edges", "lone n.edges").replace("for 4 Node", "for exactly 2 Node");

        File f1 = createTempFile("v1.als", v1Src);
        File f2 = createTempFile("v2.als", v2Src);

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        m.mergeSigs(v1, v2);
        new CommandGenerator(m).generateDiffCommand(v1, v2, 0, 0, 3, true, Analysis.SemDiff);

        List<ConstraintInfo> c1 = m.getC1Constraints();
        assertTrue("The global fact should be recorded as FACT",
                c1.stream().anyMatch(c -> c.origin() == ConstraintOrigin.FACT && c.pos().y == 2));
        assertTrue("The run predicate should be recorded as COMMAND_PREDICATE",
                c1.stream().anyMatch(c -> c.origin() == ConstraintOrigin.COMMAND_PREDICATE && c.pos().y == 3));
        assertFalse("No constraint should span more than the conjunct it came from",
                c1.stream().anyMatch(c -> c.hasSourcePos() && c.pos().y2 - c.pos().y > 0));

        ConstraintInfo scopeBound = m.getC2Constraints().stream()
                .filter(c -> c.origin() == ConstraintOrigin.SCOPE_BOUND).findFirst().orElse(null);
        assertNotNull("The exact scope of v2 should be recorded", scopeBound);
        assertEquals("A scope bound should be blamed on the command's scope, not on a signature", 4,
                scopeBound.pos().y);
        Map<String,String> v2Sources = new LinkedHashMap<>();
        v2Sources.put(scopeBound.pos().filename, v2Src);
        assertEquals("exactly 2 Node", DiffExplanation.sourceText(scopeBound.pos(), v2Sources));
    }

    /**
     * The witness determines which conjuncts are violated, so an explanation has
     * to be recomputed for every instance and must know which instance it belongs
     * to.
     */
    @Test
    public void testExplanationIsBoundToItsWitness() throws Exception {
        File f1 = createTempFile("v1.als", "sig B {}\nsig A { f: one B }");
        File f2 = createTempFile("v2.als", "sig B {}\nsig A { f: lone B }");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);
        Command diffCommand = new CommandGenerator(m).generateDiffCommand(v1, v2, -1, -1, 3, true, Analysis.SemDiff);

        A4Solution first = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, new A4Options());
        assertTrue(first.satisfiable());

        DiffExplanation.Explanation e1 = DiffExplanation.explain(first, m, Analysis.SemDiff);
        assertTrue("Explanation belongs to the witness it was computed from", e1.isFor(first));
        assertTrue("A SemDiff witness must violate at least one c1 conjunct", e1.isComplete());
        assertTrue("Nothing on the c2 side is violated by a SemDiff witness", e1.violatedC2().isEmpty());

        A4Solution second = first.next();
        if (second.satisfiable() && second != first) {
            assertFalse("A stale explanation must not claim to explain the next witness", e1.isFor(second));
            DiffExplanation.Explanation e2 = DiffExplanation.explain(second, m, Analysis.SemDiff);
            assertTrue(e2.isFor(second));
            assertTrue("Every witness of the difference must have an explanation", e2.isComplete());
        }
    }

    /**
     * A conjunct that is violated by every instance of the difference is a
     * witness-independent explanation; one that merely happens to be violated by
     * the instance on screen is not.
     */
    @Test
    public void testViolatedByEveryWitness() throws Exception {
        File f1 = createTempFile("v1.als", "sig B {}\nsig A { f: one B }");
        File f2 = createTempFile("v2.als", "sig B {}\nsig A { f: lone B }");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);
        A4Options opt = new A4Options();
        Command diffCommand = new CommandGenerator(m).generateDiffCommand(v1, v2, -1, -1, 3, true, Analysis.SemDiff);

        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, opt);
        assertTrue(sol.satisfiable());

        ConstraintInfo fieldMult = DiffExplanation.getViolatedConstraints(sol, m.getC1Constraints()).stream()
                .filter(c -> c.origin() == ConstraintOrigin.FIELD_MULTIPLICITY).findFirst().orElse(null);
        assertNotNull(fieldMult);

        // "one B" is the only thing v2 relaxes, so every instance of the difference
        // has to violate it
        assertTrue("The relaxed multiplicity is violated by every witness",
                DiffExplanation.isViolatedByEveryWitness(sigs, diffCommand, opt, fieldMult));
    }

    /**
     * A field that is mutable in only one of the two versions becomes mutable in
     * the merged model; the static side is constrained by a frame condition. A
     * witness that changes the field violates that frame condition, and the
     * state it first changes in should be reported.
     */
    @Test
    public void testTemporalFrameConditionViolation() throws Exception {
        File f1 = createTempFile("v1.als", "sig S { f: lone S }\nrun {} for 2 S\n");
        File f2 = createTempFile("v2.als", "sig S { var f: lone S }\nrun {} for 2 S\n");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);
        Command diffCommand = new CommandGenerator(m).generateDiffCommand(v1, v2, 0, 0, -1, true, Analysis.SemDiff);

        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, new A4Options());
        assertTrue("Making a field mutable adds instances", sol.satisfiable());
        assertTrue("The witness should be a trace", sol.isTemporal());

        DiffExplanation.Explanation e = DiffExplanation.explain(sol, m, Analysis.SemDiff);
        assertTrue(e.isComplete());

        ConstraintInfo frame = e.violatedC1().stream().filter(c -> c.origin() == ConstraintOrigin.FIELD_FRAME)
                .findFirst().orElse(null);
        assertNotNull("The witness must violate the frame condition of the static version", frame);
        assertTrue("The frame condition is blamed on the field declaration", frame.hasSourcePos());
        assertEquals(1, frame.pos().y);
        assertTrue("The transition in which the field changes should be reported",
                DiffExplanation.firstViolatingState(sol, frame) >= 0);
    }

    /**
     * For a violated "always" fact the tool should point at the first state of
     * the trace in which it fails, which need not be the initial state.
     */
    @Test
    public void testFirstViolatingStateOfTemporalFact() throws Exception {
        File f1 = createTempFile("v1.als",
                "one sig S { var f: lone S }\nfact { some S.f }\nfact { always (some S.f) }\nrun {} for 1 S\n");
        File f2 = createTempFile("v2.als", "one sig S { var f: lone S }\nfact { some S.f }\nrun {} for 1 S\n");

        Module v1 = CompUtil.parseEverything_fromFile(rep, null, f1.getAbsolutePath());
        Module v2 = CompUtil.parseEverything_fromFile(rep, null, f2.getAbsolutePath());

        ModuleMerger m = new ModuleMerger();
        Collection<Sig> sigs = m.mergeSigs(v1, v2);
        Command diffCommand = new CommandGenerator(m).generateDiffCommand(v1, v2, 0, 0, -1, true, Analysis.SemDiff);

        A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, sigs, diffCommand, new A4Options());
        assertTrue(sol.satisfiable());

        ConstraintInfo always = DiffExplanation.explain(sol, m, Analysis.SemDiff).violatedC1().stream()
                .filter(c -> c.origin() == ConstraintOrigin.FACT && c.pos().y == 3).findFirst().orElse(null);
        assertNotNull("The 'always' fact of v1 must be violated", always);
        // "some S.f" holds initially (the other fact forces it), so the first
        // violating state must be a later one
        assertEquals(1, DiffExplanation.firstViolatingState(sol, always));
    }

    private File createTempFile(String name, String content) throws IOException {
        File f = File.createTempFile("alloy_diff_", name);
        f.deleteOnExit();
        try (FileWriter fw = new FileWriter(f)) {
            fw.write(content);
        }
        return f;
    }
}
