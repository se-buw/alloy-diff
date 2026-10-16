package org.alloytools.alloy.diff;

import static edu.mit.csail.sdg.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprUnary.Op;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.ast.Type;
import edu.mit.csail.sdg.ast.Type.ProductType;
import edu.mit.csail.sdg.ast.VisitQuery;

public class ModuleMerger {

	/**
	 * merged signatures
	 */
	protected Map<String, Sig> sigs;
	/**
	 * optional, merged signature expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v1SigExpr;
	/**
	 * optional, merged field expressions for signatures from v1 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v1FieldExpr;
	/**
	 * inheritance information of v1 (not merged; on original signatures)
	 */
	protected InheritanceUtil v1iu;
	/**
	 * optional, merged signature expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v2SigExpr;
	/**
	 * optional, merged field expressions for signatures from v2 (to simulate
	 * inheritance)
	 */
	protected Map<String, Expr> v2FieldExpr;
	/**
	 * inheritance information of v2 (not merged; on original signatures)
	 */
	protected InheritanceUtil v2iu;
	/**
	 * constraints to ensure instances of v1 on merged signatures
	 */
	protected Expr c1;
	/**
	 * constraints to ensure instances of v2 on merged signatures
	 */
	protected Expr c2;

	/**
	 * individual conjuncts of c1 with their origin metadata, for explanation
	 */
	protected List<ConstraintInfo> c1Constraints = new ArrayList<>();
	/**
	 * individual conjuncts of c2 with their origin metadata, for explanation
	 */
	protected List<ConstraintInfo> c2Constraints = new ArrayList<>();

	private record ExprPair(Expr e1, Expr e2) {
	}

	/**
	 * A lone/one/some multiplicity of an original signature with sub-signatures
	 * that still has to be added to c1 (inV1) or c2 over the inheritance
	 * expression of that signature.
	 */
	private record PendingMultiplicity(Sig merged, Sig old, boolean inV1) {
	}

	private final List<PendingMultiplicity> pendingParentMultiplicities = new ArrayList<>();

	protected Map<String, Sig> v1Sigs;
	protected Map<String, Sig> v2Sigs;

	/**
	 * workaround for Alloy bug on parsing and predicate pred/totalOrder
	 */
	private boolean inSigFactOfOrd = false;

	/**
	 * special flag for overriding signature references in fields when adding them
	 * to subsignatures
	 */
	private String sigOverrideForField;

	protected int maxInt;

	/**
	 * Tracks an individual constraint conjunct for later explanation.
	 */
	void trackConstraint(List<ConstraintInfo> list, Expr constraint, ConstraintOrigin origin) {
		list.add(new ConstraintInfo(constraint, origin));
	}

	/**
	 * Tracks an individual constraint conjunct with an explicit source position.
	 * Used for constraints whose expression is synthesized (and therefore has no
	 * usable position of its own) or rewritten over merged sigs (whose span may
	 * mix positions from both files).
	 */
	void trackConstraint(List<ConstraintInfo> list, Expr constraint, Pos pos, ConstraintOrigin origin) {
		list.add(new ConstraintInfo(constraint, pos, origin));
	}

	/**
	 * Merges signatures from v1 and v2 by creating combined Sigs for common
	 * signatures and copying unique signatures
	 *
	 * @param v1
	 * @param v2
	 * @return
	 */
	public Collection<Sig> mergeSigs(Module v1, Module v2) {
		/**
		 * merged signatures
		 */
		sigs = new LinkedHashMap<>();
		v1SigExpr = new LinkedHashMap<>();
		v1FieldExpr = new LinkedHashMap<>();
		v1iu = new InheritanceUtil(v1);
		v2SigExpr = new LinkedHashMap<>();
		v2FieldExpr = new LinkedHashMap<>();
		v2iu = new InheritanceUtil(v2);
		v1Sigs = new LinkedHashMap<>();
		v2Sigs = new LinkedHashMap<>();
		c1 = ExprConstant.TRUE;
		c2 = ExprConstant.TRUE;
		c1Constraints = new ArrayList<>();
		c2Constraints = new ArrayList<>();
		pendingParentMultiplicities.clear();
		maxInt = 0;

		// fill look-up tables
		for (Sig s : v1.getAllReachableUserDefinedSigs()) {
			v1Sigs.put(s.toString(), s);
		}
		for (Sig s : v2.getAllReachableUserDefinedSigs()) {
			v2Sigs.put(s.toString(), s);
		}

		// do merge of signatures
		for (String sName : v1Sigs.keySet()) {
			if (v2Sigs.containsKey(sName) && !(v2Sigs.get(sName) instanceof SubsetSig)) {
				// create a merged signature
				Sig s1 = v1Sigs.get(sName);
				Sig s2 = v2Sigs.get(sName);
				if (s1 instanceof PrimSig && s2 instanceof PrimSig) {
					// ignore if both sigs are abstract and have subsigs
					if (!(s1.isAbstract != null && v1iu.getSubSigs(s1) != null && s2.isAbstract != null
							&& v2iu.getSubSigs(s2) != null)) {
						sigs.put(sName, mergeSig(s1, s2));
					}
				}
			} else {
				Sig old = v1Sigs.get(sName);
				// adding signatures that are unique in v1
				if (old instanceof PrimSig) {
					// check if needed: abstract sigs with children are not needed
					if (old.isAbstract == null || v1iu.getSubSigs(old) == null) {
						// ONE to LONE (merged sig may not have exactly one atom)
						// (not for signatures with sub-signatures: the merged signature is flat
						// and the multiplicity is enforced over the sig and its sub-sigs in c1)
						Sig s = null;
						if ((old.isLone != null || old.isOne != null) && !hasSubSigs(old, v1iu)) {
							s = new PrimSig(sName, old.isVariable != null 
										? new Attr[]{Attr.LONE, Attr.VARIABLE} 
										: new Attr[]{Attr.LONE});
						} else {
							s = new PrimSig(sName, old.isVariable != null 
										? new Attr[]{Attr.VARIABLE} 
										: new Attr[]{});
						}
						sigs.put(sName, s);
						c1 = generateSigAttributeConstraints(s, old, v1iu, c1, c1Constraints);
						// closed world
						{ Expr cw = alwaysIfVar(s.no(), old.isVariable != null); trackConstraint(c2Constraints, cw, old.pos, ConstraintOrigin.CLOSED_WORLD); c2 = c2.and(cw); }
					}
				}
			}
		}
		for (String sName : v2Sigs.keySet()) {
			if (!v1Sigs.containsKey(sName) || v1Sigs.get(sName) instanceof SubsetSig) {
				Sig old = v2Sigs.get(sName);
				// adding signatures that are unique in v2
				if (old instanceof PrimSig) {
					if (old.isAbstract == null || v2iu.getSubSigs(old) == null) {
						// ONE to LONE (merged sig may not have exactly one atom)
						// (not for signatures with sub-signatures: the merged signature is flat
						// and the multiplicity is enforced over the sig and its sub-sigs in c2)
						Sig s = null;
						if ((old.isLone != null || old.isOne != null) && !hasSubSigs(old, v2iu)) {
							s = new PrimSig(sName, old.isVariable != null 
										? new Attr[]{Attr.LONE, Attr.VARIABLE} 
										: new Attr[]{Attr.LONE});
						} else {
							s = new PrimSig(sName, old.isVariable != null 
										? new Attr[]{Attr.VARIABLE} 
										: new Attr[]{});
						}
						sigs.put(sName, s);
						c2 = generateSigAttributeConstraints(s, old, v2iu, c2, c2Constraints);
						// closed world
						{ Expr cw = alwaysIfVar(s.no(), old.isVariable != null); trackConstraint(c1Constraints, cw, old.pos, ConstraintOrigin.CLOSED_WORLD); c1 = c1.and(cw); }
					}
				}
			}
		}

		// calculate signature expressions by union of self and subclasses
		buildInheritanceSigExpr(v1, v1iu, v1SigExpr);
		buildInheritanceSigExpr(v2, v2iu, v2SigExpr);

		// multiplicities of signatures with sub-signatures range over the
		// signature and its sub-signatures
		addPendingParentMultiplicities();

		// INFO we don't support merging SubsetSig and PrimSig

		// create SubsetSig as union from both modules
		for (Sig s1 : v1Sigs.values()) {
			if (s1 instanceof SubsetSig) {
				Set<Sig> ps1 = parents((SubsetSig) s1, v1iu);
				Sig s2 = v2Sigs.get(s1.label);
				if (s2 != null) {
					if (s2 instanceof SubsetSig) {
						Set<Sig> ps2 = parents((SubsetSig) s2, v2iu);
						Set<Sig> union = new LinkedHashSet<>();
						union.addAll(ps1);
						union.addAll(ps2);

						SubsetSig sub = new SubsetSig(s1.label, union, getMergedSigAttributes(s1, s2));
						sigs.put(s1.label, sub);				
						
						// suppress additional sigs in each c1/c2
						Set<Sig> notInV1 = new LinkedHashSet<>();
						Set<Sig> notInV2 = new LinkedHashSet<>();
						notInV1.addAll(ps2);
						notInV1.removeAll(ps1);
						notInV2.addAll(ps1);
						notInV2.removeAll(ps2);
						for (Sig s : notInV1) {
							{ Expr cw = alwaysIfVar(s.intersect(sub).no(), sub.isVariable != null); trackConstraint(c1Constraints, cw, ConstraintOrigin.SIG_HIERARCHY); c1 = c1.and(cw); }
						}
						for (Sig s : notInV2) {
							{ Expr cw = alwaysIfVar(s.intersect(sub).no(), sub.isVariable != null); trackConstraint(c2Constraints, cw, ConstraintOrigin.SIG_HIERARCHY); c2 = c2.and(cw); }
						}
						c1 = generateSigAttributeConstraints(sub, s1, v1iu, c1, c1Constraints);
						
						// EXACT (sig S = ...) is enforced in restoreSubSetSigHierarchy(..)
						
						c2 = generateSigAttributeConstraints(sub, s2, v2iu, c2, c2Constraints);
					} else {
						throw new RuntimeException("Cannot merge PrimSig and SubsetSig with same name: " + s1.label);
					}
				} else {
					// SubSetSig is unique in v1, add it and suppress in v2
					ExprPair cs = addUniqueSubsetSig(s1, ps1, c1, c2, c1Constraints, c2Constraints);
					c1 = cs.e1();
					c2 = cs.e2();
				}
			}
		}
		// add v2 unique SubsetSig and suppress in v1 
		for (Sig s2 : v2Sigs.values()) {			
			if (s2 instanceof SubsetSig) {
				if (sigs.get(s2.label) == null) { // we have not handled it in the above cases, i.e., it is unique in v2
					Set<Sig> ps2 = parents((SubsetSig) s2, v2iu);
					ExprPair cs = addUniqueSubsetSig(s2, ps2, c2, c1, c2Constraints, c1Constraints);
					c2 = cs.e1();
					c1 = cs.e2();
				} else if (sigs.get(s2.label) instanceof PrimSig) {
					throw new RuntimeException("Cannot merge PrimSig and SubsetSig with same name: " + s2.label);
				}
			}
		}

		// add containment of SubsetSigs in hierarchy (removed above as it could be contradicting in the two versions):
		// for sig A in B + C ... {} add c1/c2 A in B + C
		c1 = restoreSubSetSigHierarchy(v1Sigs, v1SigExpr, c1, c1Constraints);
		c2 = restoreSubSetSigHierarchy(v2Sigs, v2SigExpr, c2, c2Constraints);
	

		// add fields to merged signatures
		for (String sName : sigs.keySet()) {
			Sig s = sigs.get(sName);
			if (s instanceof PrimSig) {
				Sig s1 = v1Sigs.get(sName);
				Sig s2 = v2Sigs.get(sName);
				if (s1 != null && s2 != null) {
					mergeFields(s, mapOf(v1iu.getAllFields(s1)), mapOf(v2iu.getAllFields(s2)));
				} else if (s1 != null) {
					addFieldsOfUniqueSig(s, mapOf(v1iu.getAllFields(s1)), true);
				} else {
					addFieldsOfUniqueSig(s, mapOf(v2iu.getAllFields(s2)), false);
				}
			}
		}

		// calculate field expressions by union of fields with the same name of sub
		// signatures
		buildInheritanceFieldExpr(v1, v1iu, v1FieldExpr);
		buildInheritanceFieldExpr(v2, v2iu, v2FieldExpr);

		addSignatureFacts(v1, true);
		addSignatureFacts(v2, false);

		// disj in field declarations (not part of the field's bound expression)
		addDisjointFieldConstraints(v1, true);
		addDisjointFieldConstraints(v2, false);

		return sigs.values();
	}

	/**
	 * Adds the constraints of {@code disj} in field declarations of one version to
	 * c1 (inV1) or c2, as Alloy does in TranslateAlloyToKodkod (declarations of
	 * the fields of a signature):
	 * <ul>
	 * <li>{@code sig S { f: disj e }}: the values of f are disjoint for different
	 * atoms, {@code all a, b: S | a != b implies no a.f & b.f} (not added for
	 * {@code one} signatures, as in Alloy)</li>
	 * <li>{@code sig S { disj f, g: e }}: the fields are pairwise disjoint,
	 * {@code no f & g}</li>
	 * </ul>
	 * The constraints are built over the original signatures and fields and then
	 * translated with {@link #replaceSigRefs(Expr, boolean)}. This replaces S by
	 * its inheritance expression (S and its sub-signatures) and f by the union of
	 * its copies, exactly as for facts. As in Alloy, the constraints hold in every
	 * state if the field is declared {@code var}, and in the initial state
	 * otherwise. (Previously, {@code disj} was dropped, so c1/c2 allowed instances
	 * that violate it.)
	 */
	private void addDisjointFieldConstraints(Module orig, boolean inV1) {
		List<ConstraintInfo> constraints = inV1 ? c1Constraints : c2Constraints;
		for (Sig os : orig.getAllReachableUserDefinedSigs()) {
			for (Decl d : os.getFieldDecls()) {
				List<Expr> cs = new ArrayList<>();
				List<Pos> ps = new ArrayList<>();
				if (os.isOne == null && d.disjoint2 != null) {
					for (ExprHasName n : d.names) {
						Decl a = os.oneOf("disj_a");
						Decl b = os.oneOf("disj_b");
						Expr body = a.get().equal(b.get()).not()
								.implies(a.get().join(n).intersect(b.get().join(n)).no());
						cs.add(ExprQt.Op.ALL.make(n.pos, null, List.of(a, b), body));
						ps.add(n.pos);
					}
				}
				if (d.names.size() > 1 && d.disjoint != null) {
					for (int i = 0; i < d.names.size(); i++) {
						for (int j = i + 1; j < d.names.size(); j++) {
							cs.add(d.names.get(i).intersect(d.names.get(j)).no());
							ps.add(d.names.get(i).pos.merge(d.names.get(j).pos));
						}
					}
				}
				for (int k = 0; k < cs.size(); k++) {
					Expr c = replaceSigRefs(cs.get(k), inV1);
					if (d.isVar != null) {
						c = ExprUnary.Op.ALWAYS.make(null, c);
					}
					trackConstraint(constraints, c, ps.get(k), ConstraintOrigin.FIELD_DISJOINT);
					if (inV1) {
						c1 = c1.and(c);
					} else {
						c2 = c2.and(c);
					}
				}
			}
		}
	}

	/**
	 * Adds {@code sub in p1 + ... + pn} for every SubsetSig {@code sig sub in p1 + ... + pn}
	 * of one version.
	 * <p>
	 * The merged PrimSigs are flat (they do not extend each other), so a merged
	 * parent signature does not contain the atoms of its sub-signatures. Each
	 * PrimSig parent is therefore replaced by its inheritance expression from
	 * {@code sigExpr} (parent plus all sub-signatures), exactly as references to
	 * signatures are translated in {@link #replaceSigRefs(Expr, boolean)}.
	 * SubsetSig parents are the merged SubsetSigs themselves.
	 * <p>
	 * If a parent cannot be resolved, the containment constraint is skipped for
	 * that SubsetSig: a union with a missing operand would be too small and
	 * would wrongly exclude instances.
	 *
	 * @param oldSigs     signatures of the version (by label)
	 * @param sigExpr     inheritance expressions of the same version
	 *                    (v1SigExpr or v2SigExpr)
	 * @param cOld        current constraint of that version
	 * @param constraints tracked conjuncts of that version
	 */
	private Expr restoreSubSetSigHierarchy(Map<String, Sig> oldSigs, Map<String, Expr> sigExpr, Expr cOld,
			List<ConstraintInfo> constraints) {
		for (Sig s : oldSigs.values()) {
			if (s instanceof SubsetSig) {
				SubsetSig sub = (SubsetSig) s;
				Expr parentUnion = null;
				boolean resolved = true;
				for (Sig parent : sub.parents) {
					Expr p = mergedParentExpr(parent, sigExpr);
					if (p == null) {
						resolved = false;
						break;
					}
					parentUnion = (parentUnion == null) ? p : parentUnion.plus(p);
				}
				if (resolved && parentUnion != null) {
					Sig c = sigs.get(sub.label);
					// sig S = P1 + ... + Pn (EXACT): S equals the union of its original
					// parents. (Previously S was set equal to the flattened type-signature
					// parents, e.g., S = A for "sig T in A" and "sig S = T".)
					Expr constraint = alwaysIfVar(sub.exact ? c.equal(parentUnion) : c.in(parentUnion), c.isVariable != null);
					trackConstraint(constraints, constraint, ConstraintOrigin.SIG_HIERARCHY);
					cOld = cOld.and(constraint);
				}
			}
		}
		return cOld;
	}

	/**
	 * Expression in the merged module that denotes the atoms of an original
	 * parent signature of a SubsetSig: the merged SubsetSig for SubsetSig parents,
	 * the inheritance expression (or the merged sig) for PrimSig parents, and the
	 * built-in signature for built-in parents.
	 *
	 * @return the expression or null if the parent cannot be resolved
	 */
	private Expr mergedParentExpr(Sig parent, Map<String, Expr> sigExpr) {
		if (parent instanceof SubsetSig) {
			return sigs.get(parent.label);
		}
		Expr e = sigExpr.get(parent.label);
		if (e == null) {
			e = sigs.get(parent.label);
		}
		if (e == null) {
			e = getInternalSig(parent.label);
		}
		return e;
	}

	private ExprPair addUniqueSubsetSig(Sig oldSig, Set<Sig> newParents, Expr c1, Expr c2, List<ConstraintInfo> ownerConstraints, List<ConstraintInfo> otherConstraints) {
		List<Attr> attrs = new ArrayList<>();
		if (oldSig.isVariable != null) {
			attrs.add(Attr.VARIABLE);
		}
		if (oldSig.isLone != null || oldSig.isOne != null) {
			attrs.add(Attr.LONE);
		}
		// SOME Is not added, but enforced in c1
		if (oldSig.isAbstract != null) {
			attrs.add(Attr.ABSTRACT);
		}
		// add v1 unique SubsetSig and suppress in v2 
		SubsetSig subV1 = new SubsetSig(oldSig.label, newParents, attrs.toArray(new Attr[0]));
		// no need to call generateSigAttributeConstraints(..) as the attributes are the same and will thus enforce the same constraints
		sigs.put(oldSig.label, subV1);

		if (oldSig.isSome != null) {
			// if the sig is some then it must be some in the merged module
			Expr constraint = alwaysIfVar(subV1.some(), subV1.isVariable != null);
			trackConstraint(ownerConstraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
			c1 = c1.and(constraint);
		}
		if (oldSig.isOne != null) {
			// if the sig is one then it must be one in the merged module
			Expr constraint = alwaysIfVar(subV1.one(), subV1.isVariable != null);
			trackConstraint(ownerConstraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
			c1 = c1.and(constraint);
		}
		// EXACT is not added to unique SubsetSigs, but enforced in
		// restoreSubSetSigHierarchy(..)
		
		Expr cwConstraint = alwaysIfVar(subV1.no(), subV1.isVariable != null);
		trackConstraint(otherConstraints, cwConstraint, ConstraintOrigin.CLOSED_WORLD);
		c2 = c2.and(cwConstraint);
		return new ExprPair(c1, c2);
	}

	/**
	 * computes the union of Sigs using the plus operator
	 * 
	 * @param ps1
	 * @return
	 */
	private Expr makePlus(Set<Sig> ps1) {
		// fold ps1 with operator plus
		Expr union = null;
		for (Sig s : ps1) {
			if (union == null) {
				union = s;
			} else {
				union = union.plus(s);
			}
		}
		return union;
	}

	/**
	 * compute a set of transitive parent PrimSigs (merged sigs in new module)
	 * 
	 * @param sub1 a SubsetSig of the version described by {@code iu}
	 * @param iu   inheritance information of the version {@code sub1} comes from;
	 *             its sub-signature map is keyed by that version's Sig objects, so
	 *             passing the other version's InheritanceUtil silently loses all
	 *             sub-signatures of the parents
	 * @return
	 */
	private Set<Sig> parents(SubsetSig sub1, InheritanceUtil iu) {
		Set<Sig> parents = new LinkedHashSet<>();
		for (Sig p : iu.getFlattenedParents(sub1)) {
			Sig c = sigs.get(p.label);
			if (c != null) { // could be the case for abstract signatures
				parents.add(c);
			}
		}

		return parents;
	}

	private Map<String, Field> mapOf(Set<Field> allFields) {
		Map<String, Field> m = new LinkedHashMap<>();
		if (allFields != null) {
			for (Field f : allFields) {
				m.put(f.label, f);
			}
		}
		return m;
	}

	private void addSignatureFacts(Module orig, boolean inV1) {
		for (Sig os : orig.getAllReachableUserDefinedSigs()) {
			for (Expr of : os.getFacts()) {
				Expr mergedSig = replaceSigRefs(os, inV1);
				Decl thisDecl = mergedSig.oneOf("this");
				List<Decl> decls = new ArrayList<>();
				decls.add(thisDecl);
				if (os.label.endsWith("/Ord")) {
					inSigFactOfOrd = true;
				}
				// a signature fact block is an implicit conjunction; quantification
				// distributes over it, so each constraint in the block becomes its own
				// conjunct and keeps its own source position
				for (Expr conjunct : Conjuncts.of(of)) {
					Expr body = replaceSigRefs(conjunct, decls, inV1);
					Expr sigFact = ExprQt.Op.ALL.make(of.pos, of.closingBracket, decls, body);
					// As in Alloy (TranslateAlloyToKodkod.makeFacts), a signature fact that
					// is temporal (mentions a mutable sig/field or a temporal operator)
					// holds in every state, not only in the first one. Deciding on the
					// merged expression is safe: whatever is mutable only in the merged
					// module is framed (constant) in this version's constraint.
					if (isTemporal(sigFact)) {
						sigFact = ExprUnary.Op.ALWAYS.make(null, sigFact);
					}
					Pos pos = ConstraintInfo.sourcePos(conjunct);
					if (inV1) {
						trackConstraint(c1Constraints, sigFact, pos, ConstraintOrigin.SIG_FACT);
						c1 = c1.and(sigFact);
					} else {
						trackConstraint(c2Constraints, sigFact, pos, ConstraintOrigin.SIG_FACT);
						c2 = c2.and(sigFact);
					}
				}
				if (os.label.endsWith("/Ord")) {
					inSigFactOfOrd = false;
				}
			}
		}

	}

	/**
	 * True if {@code e} is a temporal formula in the sense of Alloy's translation
	 * (TemporalTranslator.isTemporal on the Kodkod formula): it contains a temporal
	 * operator or refers to a mutable signature or field, also through the body of
	 * a called function or predicate.
	 */
	static boolean isTemporal(Expr e) {
		Set<Func> visited = new HashSet<>();
		VisitQuery<Object> q = new VisitQuery<Object>() {

			@Override
			public Object visit(ExprUnary x) throws Err {
				switch (x.op) {
				case AFTER:
				case BEFORE:
				case PRIME:
				case HISTORICALLY:
				case ALWAYS:
				case ONCE:
				case EVENTUALLY:
					return x;
				default:
					return super.visit(x);
				}
			}

			@Override
			public Object visit(ExprBinary x) throws Err {
				switch (x.op) {
				case UNTIL:
				case SINCE:
				case TRIGGERED:
				case RELEASES:
					return x;
				default:
					return super.visit(x);
				}
			}

			@Override
			public Object visit(Sig x) throws Err {
				return x.isVariable != null ? x : null;
			}

			@Override
			public Object visit(Field x) throws Err {
				return x.isVariable != null ? x : null;
			}

			@Override
			public Object visit(ExprCall x) throws Err {
				Object ans = super.visit(x);
				if (ans == null && visited.add(x.fun)) {
					ans = x.fun.getBody().accept(this);
				}
				return ans;
			}
		};
		try {
			return e.accept(q) != null;
		} catch (Err ex) {
			return false;
		}
	}

	/**
	 * calculate field expressions by union of fields with the same name of sub
	 * signatures and fieldexpressions for SubsetSigs 
	 * 
	 * @param m
	 * @param fieldExpr
	 */
	private void buildInheritanceFieldExpr(Module m, InheritanceUtil iu, Map<String, Expr> fieldExpr) {
		for (Sig owner : iu.getParentSigs()) {
			for (Field f : owner.getFields()) {
				String id = owner.label + "." + f.label;
				// field of new signature
				Expr fu = getField(sigs.get(owner.label), f.label);
				// all fields of children signatures
				for (Sig s : iu.getSubSigs(owner)) {
					if (fu == null) {
						fu = getField(sigs.get(s.label), f.label);
					} else {
						fu = fu.plus(getField(sigs.get(s.label), f.label));
					}
				}
				fieldExpr.put(id, fu);
			}
		}
		for (Field f : iu.getFieldsFromSubsetSig()) {
			Sig owner = f.sig;
			String id = owner.label + "." + f.label;
			Expr fu = null;
			for (Sig s : iu.getFlattenedParents((SubsetSig) owner)) {
				if (fu == null) {
					fu = getField(sigs.get(s.label), f.label);
				} else {
					fu = fu.plus(getField(sigs.get(s.label), f.label));
				}
			}
			fieldExpr.put(id, fu);
		}
	}

	private void buildInheritanceSigExpr(Module m, InheritanceUtil iu, Map<String, Expr> sigExpr) {
		for (Sig parent : m.getAllReachableUserDefinedSigs()) {
			if (parent instanceof SubsetSig) {
				Expr union = null;
				for (Sig s : iu.getFlattenedParents((SubsetSig) parent)) {
					// take care of null sigs that were not added
					if (sigs.get(s.label) != null) {
						if (union == null) {
							union = sigs.get(s.label);
						} else {
							union = union.plus(sigs.get(s.label));
						}
					}
				}
				sigExpr.put(parent.label, union);
			} else {
				Set<Sig> mSubSigs = iu.getSubSigs(parent);
				if (mSubSigs != null) {
					Expr union = sigs.get(parent.label);
					for (Sig s : mSubSigs) {
						// take care of null sigs that were not added
						if (sigs.get(s.label) != null) {
							if (union == null) {
								union = sigs.get(s.label);
							} else {
								union = union.plus(sigs.get(s.label));
							}
						}
					}
					sigExpr.put(parent.label, union);
				}
			}
		}
	}

	/**
	 * Creates a merged signature and adds constraints c1 c2 for individual sigs
	 *
	 * @param s1
	 * @param s2
	 * @return
	 */
	private Sig mergeSig(Sig s1, Sig s2) {
		Attr[] attrs = getMergedSigAttributes(s1, s2);
		if (hasSubSigs(s1, v1iu) || hasSubSigs(s2, v2iu)) {
			// the merged signature is flat; lone/one/some are enforced in c1/c2 over
			// the signature and its sub-signatures
			attrs = withoutMultiplicities(attrs);
		}
		Sig s = new PrimSig(s1.label, attrs);
		c1 = generateSigAttributeConstraints(s, s1, v1iu, c1, c1Constraints);
		c2 = generateSigAttributeConstraints(s, s2, v2iu, c2, c2Constraints);

		return s;
	}

	/**
	 *
	 * TODO: only works for fields of the same arity as a workaround fields with
	 * lower arity could be padded with a singleton signature. However, this would
	 * require changing all expressions on fields.
	 * 
	 * the stack could run into a cycle: we break the cycle by adding a field
	 * with generalFieldType(...)
	 *
	 * @param mergedSig
	 * @param fields1 fields of signature mergedSig.label in v1
	 * @param fields2 fields of signature mergedSig.label in v2
	 */
	private void mergeFields(Sig mergedSig, Map<String, Field> fields1, Map<String, Field> fields2) {
		Set<String> fNames = new LinkedHashSet<String>();

		fNames.addAll(fields1.keySet());
		fNames.addAll(fields2.keySet());
		
		Set<String> processedFields = new HashSet<>();

		for (String fName : fNames) {
			Stack<String> fieldsToAdd = new Stack<>();
			if (!processedFields.contains(fName)) {
				fieldsToAdd.push(fName);
			}
			while (!fieldsToAdd.empty()) {
				String nextField = fieldsToAdd.peek();
				if (!processedFields.contains(nextField)) {
					try {
						sigOverrideForField = mergedSig.label;
						mergeField(mergedSig, fields1.get(nextField), fields2.get(nextField));
						sigOverrideForField = null;
						processedFields.add(nextField);
						fieldsToAdd.pop();
					} catch (RuntimeException e) {
						sigOverrideForField = null;
						if (e.getMessage() != null && e.getMessage().contains("Could not find merged field ")) {
							String missingField = e.getMessage().replace("Could not find merged field ", "");
							Field missingF1 = fields1.get(missingField);
							Field missingF2 = fields2.get(missingField);
							if (fieldsToAdd.contains(missingField)) {
								// We have a field cycle: break it by creating a permissive placeholder for the
								// missing dependency, using the missing field's type rather than the current field's.
								if (getField(mergedSig, missingField) == null && (missingF1 != null || missingF2 != null)) {
									// The placeholder is the declaration of the merged field: it is
									// not re-created when the missing field is merged later (only
									// its c1/c2 constraints are added). It must therefore be as
									// permissive as the field's type in both versions, and mutable
									// if the field is mutable in either version.
									Pos isVar = (missingF1 != null && missingF1.isVariable != null) ? missingF1.isVariable
											: (missingF2 != null ? missingF2.isVariable : null);
									mergedSig.addField(missingField, generalFieldType(missingF1, missingF2), isVar);
								}
								// We leave nextField on the stack and let the loop naturally retry it.
								// If nextField depends on multiple unmerged fields, this retry
								// will safely catch the next missing dependency and push it.
							} else {
								// Add the missing field to the stack to be processed first.
								fieldsToAdd.push(missingField);
							}
						} else {
							throw e;
						}
					}
				} else {
					fieldsToAdd.pop();
				}
			}
		}

	}

	/**
	 * Creates a bounding expression of arity N-1 for a field of arity N
	 * by stripping the first column of the field's type.
	 */
	private Expr boundExprForType(Type type, boolean inV1) {
		if (type == null) return UNIV;
		Map<String, Expr> sigExpr = inV1 ? v1SigExpr : v2SigExpr;
		Expr res = null;
		for (ProductType pt : type) {
			Expr prod = null;
			// Skip the first column (the owner signature) to get the bound type
			for (int i = 1; i < pt.arity(); i++) {
				String label = pt.get(i).label;
				// a column of type S contains the atoms of S and of all its
				// sub-signatures, i.e., the inheritance expression of S (the
				// merged signatures are flat)
				Expr s = sigExpr.get(label);
				if (s == null) {
					s = sigs.get(label);
				}
				if (s == null) {
					s = getInternalSig(label);
				}
				if (s == null) {
					s = UNIV;
				}
				if (prod == null) prod = s;
				else prod = prod.product(s);
			}
			if (prod == null) prod = UNIV;
			
			if (res == null) res = prod;
			else res = res.plus(prod);
		}
		return res != null ? res : UNIV;
	}

	/**
	 * A permissive declaration bound for a merged field: the union of the types
	 * of the field in both versions (without the owner column). Unary bounds are
	 * declared with "set" because a bound without multiplicity means "one" for
	 * unary fields in Alloy.
	 */
	private Expr generalFieldType(Field f1, Field f2) {
		Expr type1 = (f1 == null) ? null : boundExprForType(f1.type(), true);
		Expr type2 = (f2 == null) ? null : boundExprForType(f2.type(), false);
		Expr res;
		if (type1 == null) {
			res = type2;
		} else if (type2 == null) {
			res = type1;
		} else if (type1.isSame(type2)) {
			res = type1;
		} else {
			res = type1.plus(type2);
		}
		if (res != null && res.type().arity() == 1) {
			res = ExprUnary.Op.SETOF.make(null, res);
		}
		return res;
	}

	private void mergeField(Sig mergedSig, Field f1, Field f2) {
		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		if (f1 != null && f2 != null) { // field is in both versions
			Pos isVar = (f1.isVariable != null ? f1.isVariable : f2.isVariable);
			// Dispatch on the arity of the field, not on the syntax of the declaration:
			// e.g., "f: A -> B" (ExprBinary) and "f: set A -> B" (ExprUnary) are both
			// binary. (Previously the AST class decided, and such pairs failed with
			// "Mix of field arities".)
			int arity1 = f1.decl().expr.type().arity();
			int arity2 = f2.decl().expr.type().arity();
			if (arity1 == 1 && arity2 == 1) { // unary fields
				ExprUnary e1 = asUnaryDecl(replaceSigRefs(f1.decl().expr, names, true));
				ExprUnary e2 = asUnaryDecl(replaceSigRefs(f2.decl().expr, names, false));
				
				Expr union = e1.sub.isSame(e2.sub) ? e1.sub : e1.sub.plus(e2.sub);
				ExprUnary.Op op = getMergeOp(e1.op, e2.op);
				if (v1iu.getFieldsFromSubsetSig().contains(f1) || v2iu.getFieldsFromSubsetSig().contains(f2)) {
					op = getMergeOp(op, ExprUnary.Op.NO);
				}
				Field f = (Field) getField(mergedSig, f1.label);
				if (f == null) {
					f = mergedSig.addField(f1.label, op.make(f1.pos, union), isVar);
				}

				Decl ths = mergedSig.decl;
				Expr quantBody1 = ths.get().join(f).in(e1);
				if (v1iu.getFieldsFromSubsetSig().contains(f1)) {
					quantBody1 = ExprITE.make(f1.pos, ths.get().in(sigs.get(f1.sig.label)), quantBody1,
							ths.get().join(f).no());
				}
				Expr quantBody2 = ths.get().join(f).in(e2);
				if (v2iu.getFieldsFromSubsetSig().contains(f2)) {
					quantBody2 = ExprITE.make(f2.pos, ths.get().in(sigs.get(f2.sig.label)), quantBody2,
							ths.get().join(f).no());
				}
				Expr e1mult = ExprQt.Op.ALL.make(f1.pos, f1.closingBracket, List.of(ths), quantBody1);
				Expr e2mult = ExprQt.Op.ALL.make(f2.pos, f2.closingBracket, List.of(ths), quantBody2);

				{ Expr fc = alwaysIfVar(e1mult, mutable(mergedSig, f)); trackConstraint(c1Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(fc); }
				if (f1.isVariable == null && f.isVariable != null) {
					// the field is static in this version: its whole relation must not change (not only for the atoms of the sig in the first state)
					{ Expr fc = fieldFrame(f); trackConstraint(c1Constraints, fc, f1.pos, ConstraintOrigin.FIELD_FRAME); c1 = c1.and(fc); }
				}
				{ Expr fc = alwaysIfVar(e2mult, mutable(mergedSig, f)); trackConstraint(c2Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(fc); }
				if (f2.isVariable == null && f.isVariable != null) {
					// Expr frameBody2 = ExprUnary.Op.ALWAYS.make(null, ExprBinary.Op.EQUALS.make(null, null, ExprUnary.Op.PRIME.make(null, ths.get().join(f)), ths.get().join(f)));
					{ Expr fc = fieldFrame(f); trackConstraint(c2Constraints, fc, f2.pos, ConstraintOrigin.FIELD_FRAME); c2 = c2.and(fc); }
				}
			} else if (arity1 > 1 && arity2 > 1 && arity1 == arity2) { // relational
																										// fields
				Expr e1 = replaceSigRefs(f1.decl().expr, names, true);
				Expr e2 = replaceSigRefs(f2.decl().expr, names, false);
				Field f = (Field) getField(mergedSig, f1.label);
				if (f == null) {
					boolean fromSubset = v1iu.getFieldsFromSubsetSig().contains(f1)
							|| v2iu.getFieldsFromSubsetSig().contains(f2);
					if (e1.isSame(e2) && !fromSubset) {
						f = mergedSig.addField(f1.label, e1, isVar);
					} else if (e1.isSame(e2)) {
						// a field of a SubsetSig is empty for atoms outside the SubsetSig;
						// arrow multiplicities in the declaration would contradict that.
						// They are enforced in c1/c2 below (only for atoms in the SubsetSig).
						f = mergedSig.addField(f1.label, replaceArrows(relationOf(e1)), isVar);
					} else {
						// "set A -> B" is declared as "A -> B" (Alloy allows only "set" in
						// front of a relation of arity > 1; it adds no constraint)
						Expr r1 = replaceArrows(relationOf(e1));
						Expr r2 = replaceArrows(relationOf(e2));
						Expr union = r1.isSame(r2) ? r1 : r1.plus(r2);
						f = mergedSig.addField(f1.label, union, isVar);
					}
				}

				Decl ths = mergedSig.decl;
				Expr quantBody1 = ths.get().join(f).in(e1);
				if (v1iu.getFieldsFromSubsetSig().contains(f1)) {
					quantBody1 = ExprITE.make(f1.pos, ths.get().in(sigs.get(f1.sig.label)),
							ths.get().join(f).in(e1), ths.get().join(f).no());
				}
				Expr quantBody2 = ths.get().join(f).in(e2);
				if (v2iu.getFieldsFromSubsetSig().contains(f2)) {
					quantBody2 = ExprITE.make(f2.pos, ths.get().in(sigs.get(f2.sig.label)),
							ths.get().join(f).in(e2), ths.get().join(f).no());
				}
				Expr e1mult = ExprQt.Op.ALL.make(f1.pos, f1.closingBracket, List.of(ths), quantBody1);
				Expr e2mult = ExprQt.Op.ALL.make(f2.pos, f2.closingBracket, List.of(ths), quantBody2);

				{ Expr fc = alwaysIfVar(e1mult, mutable(mergedSig, f)); trackConstraint(c1Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(fc); }
				if (f1.isVariable == null && f.isVariable != null) {
					// the field is static in this version: its whole relation must not change (not only for the atoms of the sig in the first state)
					{ Expr fc = fieldFrame(f); trackConstraint(c1Constraints, fc, f1.pos, ConstraintOrigin.FIELD_FRAME); c1 = c1.and(fc); }
				}
				{ Expr fc = alwaysIfVar(e2mult, mutable(mergedSig, f)); trackConstraint(c2Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(fc); }
				if (f2.isVariable == null && f.isVariable != null) {
					{ Expr fc = fieldFrame(f); trackConstraint(c2Constraints, fc, f2.pos, ConstraintOrigin.FIELD_FRAME); c2 = c2.and(fc); }
				}
			} else {
				throw new RuntimeException("Mix of field arities " + f1.pos);
			}
		} else if (f1 != null) {
			addUniqueField(mergedSig, f1, true);
		} else if (f2 != null) {
			addUniqueField(mergedSig, f2, false);
		}
	}

	/**
	 * The declaration expression of a unary field as a multiplicity expression.
	 * Alloy's parser declares a unary field with a multiplicity (one by default);
	 * other unary expressions are read as "one e", as in Alloy.
	 */
	private static ExprUnary asUnaryDecl(Expr e) {
		if (e instanceof ExprUnary) {
			ExprUnary u = (ExprUnary) e;
			switch (u.op) {
			case SETOF:
			case LONEOF:
			case ONEOF:
			case SOMEOF:
				return u;
			default:
				break;
			}
		}
		return (ExprUnary) ExprUnary.Op.ONEOF.make(e.pos, e);
	}

	/**
	 * The relation of a declaration of arity > 1 without a leading multiplicity,
	 * e.g., "A -> B" for "set A -> B". (Alloy rejects lone/one/some in front of a
	 * relation of arity > 1; they are handled the same way for robustness.)
	 */
	private static Expr relationOf(Expr e) {
		if (e instanceof ExprUnary) {
			ExprUnary u = (ExprUnary) e;
			switch (u.op) {
			case SETOF:
			case LONEOF:
			case ONEOF:
			case SOMEOF:
				return u.sub;
			default:
				break;
			}
		}
		return e;
	}

	/**
	 * Frame condition for a field that is static in one version but mutable in
	 * the merged module: the whole relation of the merged field stays the same in
	 * all states. (Quantifying over the atoms of the signature, as before, only
	 * covers the atoms that are in a mutable signature in the first state.)
	 */
	private Expr fieldFrame(Field f) {
		return ExprUnary.Op.ALWAYS.make(null, ExprBinary.Op.EQUALS.make(null, null, ExprUnary.Op.PRIME.make(null, f), f));
	}

	/**
	 * True if a field of the merged signature may change over time, i.e., the
	 * merged field or the merged signature is mutable. Alloy enforces the
	 * declaration of a field of a mutable signature in every state, also if the
	 * field itself is static (atoms that join the signature later must satisfy
	 * the declaration as well), so the declaration constraints in c1/c2 are then
	 * wrapped in always.
	 */
	private boolean mutable(Sig mergedSig, Field f) {
		return f.isVariable != null || mergedSig.isVariable != null;
	}

	/**
	 * adding fields of a unique signature of eihter one version. No need to
	 * restrict c1 and c2 as instnaces of the signature wouldn't exist in the other
	 * version
	 * 
	 * @param s
	 * @param fields
	 * @param inV1
	 */
	private void addFieldsOfUniqueSig(Sig s, Map<String, Field> fields, boolean inV1) {
		for (String fName : fields.keySet()) {
			Stack<String> fieldsToAdd = new Stack<>();
			if (getField(s, fName) == null) {
				fieldsToAdd.push(fName);
			}
			while (!fieldsToAdd.empty()) {
				String nextField = fieldsToAdd.peek();
				if (getField(s, nextField) == null) {
					Field f = fields.get(nextField);
					try {
						sigOverrideForField = s.label;
						Expr bound = replaceSigRefs(f.decl().expr, List.of(s.decl), inV1);
						
						if ((inV1 ? v1iu : v2iu).getFieldsFromSubsetSig().contains(f)) {
							// we have a field from a SubsetSig
							if (bound instanceof ExprUnary) {
								// operator needs to be adapted
								Expr origBound = bound;
								ExprUnary.Op op = getMergeOp(((ExprUnary) bound).op, Op.NO);
								bound = op.make(f.pos, ((ExprUnary) bound).sub);
								// case 1: add the now optional field 
								Field merged = s.addField(f.label, bound, f.isVariable);		
								if (inV1) {
									Decl ths = s.decl;
									Expr quantBody1 = ths.get().join(merged).in(origBound);
									quantBody1 = ExprITE.make(f.pos, ths.get().in(sigs.get(f.sig.label)),
											quantBody1, ths.get().join(merged).no());
									Expr e1mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody1);
									{ Expr fc = alwaysIfVar(e1mult, f.isVariable != null || s.isVariable != null); trackConstraint(c1Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(fc); }
								} else {
									Decl ths = s.decl;
									Expr quantBody2 = ths.get().join(merged).in(origBound);
									quantBody2 = ExprITE.make(f.pos, ths.get().in(sigs.get(f.sig.label)),
											quantBody2, ths.get().join(merged).no());
									Expr e2mult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody2);
									{ Expr fc = alwaysIfVar(e2mult, f.isVariable != null || s.isVariable != null); trackConstraint(c2Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(fc); }
								}
							} else {
								// case 2: relational field. Arrow multiplicities (e.g. "B -> one C")
								// would force the field to be non-empty for atoms outside the
								// SubsetSig as well, contradicting "no this.f" for those atoms. Declare
								// it with plain arrows and enforce the original declaration only for
								// atoms in the SubsetSig.
								Expr declared = replaceArrows(bound);
								Field merged = s.addField(f.label, declared, f.isVariable);
								Decl ths = s.decl;
								Expr quantBody = declared.isSame(bound)
										? ths.get().in(sigs.get(f.sig.label)).or(ths.get().join(merged).no())
										: ExprITE.make(f.pos, ths.get().in(sigs.get(f.sig.label)),
												ths.get().join(merged).in(bound), ths.get().join(merged).no());
								Expr emult = ExprQt.Op.ALL.make(f.pos, f.closingBracket, List.of(ths), quantBody);
								// field needs to be suppressed
								if (inV1) {
									{ Expr fc = alwaysIfVar(emult, f.isVariable != null || s.isVariable != null); trackConstraint(c1Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(fc); }
								} else {
									{ Expr fc = alwaysIfVar(emult, f.isVariable != null || s.isVariable != null); trackConstraint(c2Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(fc); }
								}
							}
						} else {
							// case 3: just add field as is
							s.addField(f.label, bound, f.isVariable);
						}
						sigOverrideForField = null;
						fieldsToAdd.pop();

					} catch (RuntimeException e) {
						if (e.getMessage() != null && e.getMessage().contains("Could not find merged field ")) {
							String missingField = e.getMessage().replace("Could not find merged field ", "");
							fieldsToAdd.push(missingField);
						} else {
							throw e;
						}
					}
				} else {
					fieldsToAdd.pop();
				}
			}
		}
	}

	/**
	 * adds a field to a common signature that only exists in v1 or v2 but not in
	 * both
	 * 
	 * @param mergedSig
	 * @param field
	 * @param inC1
	 */
	private void addUniqueField(Sig mergedSig, Field field, boolean inC1) {
		List<Decl> names = new ArrayList<>();
		names.add(mergedSig.decl);

		Field f;
		Expr e = replaceSigRefs(field.decl().expr, names, inC1);
		if (e instanceof ExprUnary) {
			ExprUnary.Op op = getMergeOp(((ExprUnary) e).op, ExprUnary.Op.NO);
			f = mergedSig.addField(field.label, op.make(field.pos, ((ExprUnary) e).sub), field.isVariable);
			Decl ths = mergedSig.decl;
			if (inC1) {
				Expr quantBody = ths.get().join(f).in(e);
				// restriction of fields from SubsetSigs
				if (v1iu.getFieldsFromSubsetSig().contains(field)) {
					quantBody = ExprITE.make(field.pos, ths.get().in(sigs.get(field.sig.label)), quantBody,
							ths.get().join(f).no());
				}
				Expr e1mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
				{ Expr fc = alwaysIfVar(e1mult, field.isVariable != null || mergedSig.isVariable != null); trackConstraint(c1Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(fc); }

				{ Expr fc = alwaysIfVar(f.decl().get().no(), field.isVariable != null); trackConstraint(c2Constraints, fc, field.pos, ConstraintOrigin.CLOSED_WORLD); c2 = c2.and(fc); }
			} else {
				{ Expr fc = alwaysIfVar(f.decl().get().no(), field.isVariable != null); trackConstraint(c1Constraints, fc, field.pos, ConstraintOrigin.CLOSED_WORLD); c1 = c1.and(fc); }

				Expr quantBody = ths.get().join(f).in(e);
				// restriction of fields from SubsetSigs
				if (v2iu.getFieldsFromSubsetSig().contains(field)) {
					quantBody = ExprITE.make(field.pos, ths.get().in(sigs.get(field.sig.label)), quantBody,
							ths.get().join(f).no());
				}

				Expr e2mult = ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody);
				{ Expr fc = alwaysIfVar(e2mult, field.isVariable != null || mergedSig.isVariable != null); trackConstraint(c2Constraints, fc, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(fc); }
			}
		} else if (e instanceof ExprBinary) {
			// The field only exists in one version and must be empty in the other one
			// (closed world). Arrow multiplicities such as "B -> one C" in the
			// declaration would force the field to be non-empty for every atom of the
			// merged signature, contradicting the closed-world constraint (and, for
			// fields of SubsetSigs, "no this.f" for atoms outside the SubsetSig).
			// Hence the field is declared with plain arrows and the original
			// declaration (with multiplicities) is enforced in the owner's constraint.
			Expr declared = replaceArrows(e);
			boolean relaxed = !declared.isSame(e);
			boolean fromSubset = (inC1 ? v1iu : v2iu).getFieldsFromSubsetSig().contains(field);
			f = mergedSig.addField(field.label, declared, field.isVariable);
			Expr ownerConstraint = null;
			if (relaxed || fromSubset) {
				Decl ths = mergedSig.decl;
				Expr quantBody = ths.get().join(f).in(e);
				if (fromSubset) {
					// make empty if not in SubsetSig
					quantBody = ExprITE.make(field.pos, ths.get().in(sigs.get(field.sig.label)), quantBody,
							ths.get().join(f).no());
				}
				ownerConstraint = alwaysIfVar(ExprQt.Op.ALL.make(field.pos, field.closingBracket, List.of(ths), quantBody),
						field.isVariable != null || mergedSig.isVariable != null);
			}
			if (inC1) {
				if (ownerConstraint != null) { trackConstraint(c1Constraints, ownerConstraint, ConstraintOrigin.FIELD_MULTIPLICITY); c1 = c1.and(ownerConstraint); }
				{ Expr fc = alwaysIfVar(f.decl().get().no(), field.isVariable != null); trackConstraint(c2Constraints, fc, field.pos, ConstraintOrigin.CLOSED_WORLD); c2 = c2.and(fc); }
			} else {
				if (ownerConstraint != null) { trackConstraint(c2Constraints, ownerConstraint, ConstraintOrigin.FIELD_MULTIPLICITY); c2 = c2.and(ownerConstraint); }
				{ Expr fc = alwaysIfVar(f.decl().get().no(), field.isVariable != null); trackConstraint(c1Constraints, fc, field.pos, ConstraintOrigin.CLOSED_WORLD); c1 = c1.and(fc); }
			}
		}
	}

	private List<ExprHasName> replaceSigRefs(ConstList<? extends ExprHasName> es, boolean inV1) {
		List<ExprHasName> l = new ArrayList<>();
		for (Expr e : es) {
			l.add((ExprHasName) replaceSigRefs(e, inV1));
		}
		return l;
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 *
	 * @param expr
	 * @return
	 */
	protected Expr replaceSigRefs(Expr expr, boolean inV1) {
		return replaceSigRefs(expr, new ArrayList<>(), inV1);
	}

	/**
	 * Replaces occurrences of old signatures in the expression by the merged
	 * signatures
	 *
	 * @param expr
	 * @param names list of local names to use for ExprVar
	 * @return
	 */
	private Expr replaceSigRefs(Expr expr, List<Decl> names, boolean inV1) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceSigRefs(ue.sub, List.copyOf(names), inV1));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			return be.op.make(be.pos, be.closingBracket, replaceSigRefs(be.left, List.copyOf(names), inV1),
					replaceSigRefs(be.right, List.copyOf(names), inV1));
		case "PrimSig":
			PrimSig ps = (PrimSig) expr;
			// workaround for totalOrder bug
			if (inSigFactOfOrd && ps.label.endsWith("/Ord")) {
				for (Decl d : names) {
					for (ExprHasName n : d.names) {
						if (n.label.equals("this")) {
							return n;
						}
					}
				}
			}
			// expressions taking care of inheritance override normal signatures
			if (inV1 && v1SigExpr.get(ps.label) != null) {
				return v1SigExpr.get(ps.label);
			} else if (!inV1 && v2SigExpr.get(ps.label) != null) {
				return v2SigExpr.get(ps.label);
			}
			// return merged signature
			Sig s = sigs.get(ps.label);
			if (s == null) {
				s = getInternalSig(ps.label);
				if (s == null) {
					throw new RuntimeException("Could not find merged signarure " + ps.label);
				}
			}
			return s;
		case "SubsetSig":
			SubsetSig sub = (SubsetSig) expr;
			return sigs.get(sub.label);
		case "ExprList":
			ExprList el = (ExprList) expr;
			List<Expr> l = new ArrayList<Expr>();
			for (Expr e : el.args) {
				l.add(replaceSigRefs(e, List.copyOf(names), inV1));
			}
			return ExprList.make(el.pos, el.closingBracket, el.op, l);
		case "ExprQt":
			ExprQt eq = (ExprQt) expr;
			List<Decl> allDecls = new ArrayList<Decl>(names);
			List<Decl> qtDecls = new ArrayList<Decl>();
			for (Decl d : eq.decls) {
				Decl newD = new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names, inV1),
						replaceSigRefs(d.expr, allDecls, inV1));
				qtDecls.add(newD);
				allDecls.add(newD);
			}
			return eq.op.make(eq.pos, eq.closingBracket, qtDecls, replaceSigRefs(eq.sub, allDecls, inV1));
		case "ExprVar":
			ExprVar ev = (ExprVar) expr;
			for (Decl d : names) {
				for (ExprHasName n : d.names) {
					if (n.label.equals(ev.label)) {
						return n;
					}
				}
			}
			Type t = ev.type();
			if (ev.label.equals("this")) {
				// TODO check whether this is always right
				return getExprVarToSig(ev, inV1);
			}
			ExprVar ret = ExprVar.make(ev.pos, ev.label, replaceSigRefs(t, inV1));
			return ret;
		case "Field":
			Field f = (Field) expr;
			String sigName = sigOverrideForField != null ? sigOverrideForField : f.sig.label;
			// check whether we have field expressions to take care of inheritance
			String key = sigName + "." + f.label;
			if (inV1 && v1FieldExpr.get(key) != null) {
				return v1FieldExpr.get(key);
			} else if (!inV1 && v2FieldExpr.get(key) != null) {
				return v2FieldExpr.get(key);
			}
			// return reference to merged field
			Expr res = getField(sigs.get(sigName), f.label);
			if (res == null) {
				throw new RuntimeException("Could not find merged field " + f.label);
			}
			return res;
		case "ExprConstant":
			maxInt = Math.max(maxInt, ((ExprConstant) expr).num());
			return expr;
		case "ExprCall":
			//
			ExprCall ec = (ExprCall) expr;
			List<Expr> args = new ArrayList<>();
			for (Expr c : ec.args) {
				args.add(replaceSigRefs(c, names, inV1));
			}
			// FIXME pass names as parameter?
			Expr nec = ExprCall.make(ec.pos, ec.closingBracket, replaceSigRefs(ec.fun, inV1), args, 0);
			return nec;
		case "ExprLet":
			ExprLet let = (ExprLet) expr;
			ExprVar evar = (ExprVar) replaceSigRefs(let.var, inV1);

			List<ExprHasName> letNames = new ArrayList<>();
			letNames.add(evar);
			Decl d = new Decl(null, null, null, letNames, evar);
			names = new ArrayList<>(names);
			names.add(d);
			return ExprLet.make(let.pos, evar, replaceSigRefs(let.expr, names, inV1),
					replaceSigRefs(let.sub, names, inV1));
		case "ExprITE":
			ExprITE ite = (ExprITE) expr;
			return ExprITE.make(ite.pos, replaceSigRefs(ite.cond, List.copyOf(names), inV1),
					replaceSigRefs(ite.left, List.copyOf(names), inV1),
					replaceSigRefs(ite.right, List.copyOf(names), inV1));
		default:
			System.out.println(expr.getClass().getSimpleName());
			throw new RuntimeException(
					"Error in replaceSigRefs for: " + expr.getClass().getSimpleName() + "\nat " + expr.pos);
		}
	}

	private Func replaceSigRefs(Func fun, boolean inV1) {
		List<Decl> decls = new ArrayList<Decl>();
		// REVIEW some functions have a decl that refernces a signature as this
		// ..\models-master\ietf-rfcs\rfc7617-BasicAuth\basic-auth.als
		// fun Charset.binary[ s : String ] : Binary {this.maps[s]}
		// Handle functions that have a decl referencing a signature as 'this'
		// e.g. fun Charset.binary[ s : String ] : Binary { this.maps[s] }
		for (Decl d : fun.decls) {
			decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, replaceSigRefs(d.names, inV1),
					replaceSigRefs(d.expr, decls, inV1)));
		}
		Func fun2 = new Func(fun.pos, fun.label, decls, replaceSigRefs(fun.returnDecl, decls, inV1),
				replaceSigRefs(fun.getBody(), decls, inV1));
		return fun2;
	}

	private ExprVar getExprVarToSig(ExprVar ev, boolean inV1) {
		ProductType pt = ev.type().iterator().next();
		if (pt.arity() > 1) {
			throw new RuntimeException("Arity > 1 when resolving a \"this\" expression");
		}
		String sigLabel = pt.get(0).label;
		// First try the sig expression (handles abstract sigs with subsigs
		// that are not directly in the sigs map, e.g. when both modules have
		// the same abstract sig with children)
		Expr sigExpr = (inV1 ? v1SigExpr : v2SigExpr).get(sigLabel);
		if (sigExpr != null) {
			return ExprVar.make(ev.pos, "this", sigExpr.type());
		}
		// Fall back to the merged sig
		Sig s = sigs.get(sigLabel);
		if (s == null) {
			s = getInternalSig(sigLabel);
			if (s == null) {
				throw new RuntimeException("Signature " + sigLabel + " not found in merged signature map.");
			}
		}

		return (ExprVar) s.decl.get();
	}

	private Type replaceSigRefs(Type t, boolean inV1) {
		for (ProductType pt : t) {
			Type product = null;
			for (int i = 0; i < pt.arity(); i++) {
				Expr s = (inV1 ? v1SigExpr : v2SigExpr).get(pt.get(i).label);
				if (s == null) {
					s = sigs.get(pt.get(i).label);
				}
				if (s == null) {
					s = getInternalSig(pt.get(i).label);
					if (s == null) {
						throw new RuntimeException(
								"Signature " + pt.get(i).label + " not found in merged signature map.");
					}
				}
				if (product == null) {
					product = s.type();
				} else {
					product = product.product(s.type());
				}
			}
			return product;
		}
		if (t.is_bool) {
			return Type.FORMULA;
		}
		throw new RuntimeException("Unhandled case at end of replaceSigRefs(Type t)");
	}

	private Sig getInternalSig(String label) {
		switch (label) {
		case "univ":
			return Sig.UNIV;
		case "Int":
			return Sig.SIGINT;
		case "seq/Int":
			return Sig.SEQIDX;
		case "String":
			return Sig.STRING;
		case "none":
			return Sig.NONE;
		default:
			return null;
		}

	}

	private Expr getField(Sig sig, String label) {
		if (sig != null) {
			for (Field f : sig.getFields()) {
				if (f.label.equals(label)) {
					return f;
				}
			}
		}
		return null;
	}

	/**
	 * replaces any arrow inside binary expressions by the default arrow "->"
	 * 
	 * IMPORTANT this operates on already merged and replaced expressions
	 * 
	 * some expressions (that may not contain arrows are returned as is)
	 *
	 * @param expr
	 * @return
	 */
	private Expr replaceArrows(Expr expr) {
		switch (expr.getClass().getSimpleName()) {
		case "ExprUnary":
			ExprUnary ue = (ExprUnary) expr;
			return ue.op.make(ue.pos, replaceArrows(ue.sub));
		case "ExprBinary":
			ExprBinary be = (ExprBinary) expr;
			if (be.op.isArrow) {
				return ExprBinary.Op.ARROW.make(be.pos, be.closingBracket, replaceArrows(be.left),
						replaceArrows(be.right));
			} else {
				return be.op.make(be.pos, be.closingBracket, replaceArrows(be.left), replaceArrows(be.right));
			}
		case "ExprList":
			ExprList el = (ExprList) expr;
			List<Expr> l = new ArrayList<Expr>();
			for (Expr e : el.args) {
				l.add(replaceArrows(e));
			}
			return ExprList.make(el.pos, el.closingBracket, el.op, l);
		case "ExprITE":
			ExprITE ite = (ExprITE) expr;
			return ExprITE.make(ite.pos, ite.cond, replaceArrows(ite.left), replaceArrows(ite.right));
		case "ExprLet":
			ExprLet let = (ExprLet) expr;
			return ExprLet.make(let.pos, let.var, let.expr, replaceArrows(let.sub));
		case "PrimSig":
		case "SubsetSig":
		case "Field":
		case "ExprVar":
		case "ExprQt":
		case "ExprConstant":
		case "ExprCall":
			// no arrows with multiplicities at the top level of these expressions
			return expr;
		default:
			throw new RuntimeException(
					"replaceArrows(..) unhandled expr: " + expr.getClass().getSimpleName() + " in " + expr.pos);
		}
	}

	/**
	 * Computes least upper bound of two operators
	 *
	 * @param op
	 * @param op2
	 * @return
	 */
	private ExprUnary.Op getMergeOp(ExprUnary.Op op, ExprUnary.Op op2) {
		switch (op) {
		case SETOF:
			return ExprUnary.Op.SETOF;
		case SOMEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case LONEOF:
				return ExprUnary.Op.SETOF;
			case NO:
				return ExprUnary.Op.SETOF;
			default:
				// this covers both the some and the one operator
				return ExprUnary.Op.SOMEOF;
			}
		case LONEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SETOF;
			default:
				// this covers both the lone and the one operator
				return ExprUnary.Op.LONEOF;
			}
		case ONEOF:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SOMEOF;
			case LONEOF:
				return ExprUnary.Op.LONEOF;
			case NO:
				return ExprUnary.Op.LONEOF;
			default:
				// this covers the one operator
				return ExprUnary.Op.ONEOF;
			}
		case NO:
			switch (op2) {
			case SETOF:
				return ExprUnary.Op.SETOF;
			case SOMEOF:
				return ExprUnary.Op.SETOF;
			case LONEOF:
				return ExprUnary.Op.LONEOF;
			case NO:
				return ExprUnary.Op.NO;
			case ONEOF:
				return ExprUnary.Op.LONEOF;
			default:
				// this covers the one operator
				return ExprUnary.Op.NO;
			}
		default:
			return ExprUnary.Op.SETOF;
		}
	}

	/**
	 * create constraints for attributes
	 *
	 * @param s
	 * @param old
	 * @param c
	 * @return
	 */
	/**
	 * A constraint implied by a declaration holds in every state of a trace. As in
	 * Alloy (TranslateAlloyToKodkod: TemporalTranslator.isTemporal on the
	 * declaration formula), the constraint is wrapped in always if it is temporal,
	 * i.e., refers to a mutable signature or field of the merged module or uses a
	 * temporal operator. A relation that is mutable only in the merged module is
	 * kept constant in the respective version by a frame condition, so always c is
	 * then equivalent to c. {@code isVar} is kept for callers that know that the
	 * constrained signature or field is mutable. (Previously only {@code isVar}
	 * was checked, e.g., for "f: set S" with "var sig S" the declaration only
	 * constrained the first state.)
	 */
	private Expr alwaysIfVar(Expr e, boolean isVar) {
		if (isVar || isTemporal(e)) {
			return ExprUnary.Op.ALWAYS.make(null, e);
		}
		return e;
	}



	private Expr generateSigAttributeConstraints(Sig s, Sig old, InheritanceUtil iu, Expr c, List<ConstraintInfo> constraints) {
		boolean isVar = (s.isVariable != null); // if merged sig is var (likely old was not) then constraints of old need to be wrapped in always
		boolean hasSubSigs = hasSubSigs(old, iu);
		// An abstract signature with sub-signatures has no atoms of its own. The
		// merged signature is always flat (it has no sub-signatures in the merged
		// module), so a merged "abstract" attribute has no effect and the
		// constraint is needed even if the merged signature is abstract as well.
		if (old.isAbstract != null && hasSubSigs) {
			Expr constraint = alwaysIfVar(s.no(), isVar);
			trackConstraint(constraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
			c = c.and(constraint);
		}

		if (hasSubSigs) {
			// The multiplicity of old restricts old together with all its
			// sub-signatures (in the merged module: the inheritance expression of
			// old). That expression is only available once all signatures are
			// merged, see addPendingParentMultiplicities().
			if (old.isLone != null || old.isOne != null || old.isSome != null) {
				pendingParentMultiplicities.add(new PendingMultiplicity(s, old, iu == v1iu));
			}
		} else {
			if (old.isLone != null && s.isLone == null) {
				Expr constraint = alwaysIfVar(s.lone(), isVar);
				trackConstraint(constraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
				c = c.and(constraint);
			}

			if (old.isOne != null && s.isOne == null) {
				Expr constraint = alwaysIfVar(s.one(), isVar);
				trackConstraint(constraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
				c = c.and(constraint);
			}

			if (old.isSome != null && s.isSome == null) {
				Expr constraint = alwaysIfVar(s.some(), isVar);
				trackConstraint(constraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
				c = c.and(constraint);
			}
		}

		// check if merged one is var and old was not, then we need to add a constraint that the value of the signature does not change over time
		if (old.isVariable == null && isVar) {
			Expr constraint = ExprUnary.Op.ALWAYS.make(null, ExprBinary.Op.EQUALS.make(null, null, s.prime(), s));
			trackConstraint(constraints, constraint, ConstraintOrigin.SIG_ATTRIBUTE);
			c = c.and(constraint);
		}

		return c;
	}

	/**
	 * True if {@code old} is a PrimSig with at least one sub-signature in its
	 * version.
	 */
	private boolean hasSubSigs(Sig old, InheritanceUtil iu) {
		return old instanceof PrimSig && iu.getSubSigs(old) != null && !iu.getSubSigs(old).isEmpty();
	}

	/**
	 * Adds the lone/one/some constraints of signatures with sub-signatures that
	 * were recorded by generateSigAttributeConstraints(..). Must be called after
	 * buildInheritanceSigExpr(..) for both versions: in the original module the
	 * multiplicity restricts the signature together with its sub-signatures, which
	 * in the merged (flat) module is the inheritance expression.
	 */
	private void addPendingParentMultiplicities() {
		for (PendingMultiplicity pm : pendingParentMultiplicities) {
			Sig s = pm.merged();
			Sig old = pm.old();
			InheritanceUtil iu = pm.inV1() ? v1iu : v2iu;
			Expr e = (pm.inV1() ? v1SigExpr : v2SigExpr).get(old.label);
			if (e == null) {
				e = s;
			}
			// wrap in always if any of the merged signatures in e is mutable
			boolean isVar = s.isVariable != null;
			for (Sig sub : iu.getSubSigs(old)) {
				Sig ms = sigs.get(sub.label);
				if (ms != null && ms.isVariable != null) {
					isVar = true;
				}
			}
			List<ConstraintInfo> constraints = pm.inV1() ? c1Constraints : c2Constraints;
			List<Expr> cs = new ArrayList<>();
			List<Pos> ps = new ArrayList<>();
			if (old.isLone != null) {
				cs.add(alwaysIfVar(e.lone(), isVar));
				ps.add(old.isLone);
			}
			if (old.isOne != null) {
				cs.add(alwaysIfVar(e.one(), isVar));
				ps.add(old.isOne);
			}
			if (old.isSome != null) {
				cs.add(alwaysIfVar(e.some(), isVar));
				ps.add(old.isSome);
			}
			for (int i = 0; i < cs.size(); i++) {
				trackConstraint(constraints, cs.get(i), ps.get(i), ConstraintOrigin.SIG_ATTRIBUTE);
				if (pm.inV1()) {
					c1 = c1.and(cs.get(i));
				} else {
					c2 = c2.and(cs.get(i));
				}
			}
		}
		pendingParentMultiplicities.clear();
	}

	/**
	 * Removes lone/one/some from merged attributes. Used for merged signatures
	 * that have sub-signatures in at least one version: the merged signature is
	 * flat, so a multiplicity attribute on it would restrict only the atoms that
	 * are not in a sub-signature. The multiplicities are enforced in c1/c2
	 * instead.
	 */
	private Attr[] withoutMultiplicities(Attr[] attrs) {
		List<Attr> res = new ArrayList<>();
		for (Attr a : attrs) {
			if (a != null && (a.type == Attr.AttrType.LONE || a.type == Attr.AttrType.ONE
					|| a.type == Attr.AttrType.SOME)) {
				continue;
			}
			res.add(a);
		}
		return res.toArray(new Attr[0]);
	}

	/**
	 * merges the attributes of two old signatures for a new one
	 * 
	 * if one of them is var then the merged signature is also var
	 * 
	 * for oher attributes: keep all common attributes FIXME for multiplicities is should be better to
	 * take the least upper bound (this is now handled by the generateSigAttributeConstraints(..) method)
	 * 
	 * @param s1
	 * @param s2
	 * @return
	 */
	private Attr[] getMergedSigAttributes(Sig s1, Sig s2) {
		List<Attr> attrs = new ArrayList<>();
		for (Attr a1 : s1.attributes) {
			for (Attr a2 : s2.attributes) {
				if (a1 != null && a2 != null && a1.type.equals(a2.type)) {
					// don't add EXACT attributes (if the parents are different, then EXACT would be wrong)
					// multiplicities are added below as their least upper bound
					if (!Attr.AttrType.EXACT.equals(a1.type) && !isMultiplicity(a1.type)) {
						attrs.add(a1.type.make(a1.pos));
					}
				}
			}
		}
		// least upper bound of the multiplicities (Fig. "Partial order of Alloy
		// multiplicities"), e.g., one and lone -> lone, one and some -> some, lone and
		// some -> set. The original multiplicities are added to c1/c2 by
		// generateSigAttributeConstraints(..). (Previously only a multiplicity that
		// is the same in both versions was kept, e.g., one and lone -> set.)
		Attr.AttrType mult = leastUpperBound(multiplicity(s1), multiplicity(s2));
		if (mult != null) {
			attrs.add(mult.make(null));
		}
		if ((s1.isVariable != null || s2.isVariable != null) && !containsVariable(attrs)) {
			attrs.add(Attr.AttrType.VARIABLE.make(null));
		}
		return attrs.toArray(new Attr[] {});
	}

	private static boolean isMultiplicity(Attr.AttrType t) {
		return t == Attr.AttrType.LONE || t == Attr.AttrType.ONE || t == Attr.AttrType.SOME;
	}

	/**
	 * The multiplicity of a signature: ONE, LONE, SOME, or null for set.
	 */
	private static Attr.AttrType multiplicity(Sig s) {
		if (s.isOne != null) {
			return Attr.AttrType.ONE;
		}
		if (s.isLone != null) {
			return Attr.AttrType.LONE;
		}
		if (s.isSome != null) {
			return Attr.AttrType.SOME;
		}
		return null;
	}

	/**
	 * Least upper bound of two signature multiplicities (null denotes set):
	 * one &lt;= lone &lt;= set and one &lt;= some &lt;= set.
	 */
	static Attr.AttrType leastUpperBound(Attr.AttrType m1, Attr.AttrType m2) {
		if (m1 == null || m2 == null) {
			return null;
		}
		if (m1 == m2) {
			return m1;
		}
		if (m1 == Attr.AttrType.ONE) {
			return m2;
		}
		if (m2 == Attr.AttrType.ONE) {
			return m1;
		}
		// lone and some
		return null;
	}

	private boolean containsVariable(List<Attr> attrs) {
		for (Attr a : attrs) {
			if (a != null && a.type == Attr.AttrType.VARIABLE) {
				return true;
			}
		}
		return false;
	}

	public List<ConstraintInfo> getC1Constraints() {
		return c1Constraints;
	}

	public List<ConstraintInfo> getC2Constraints() {
		return c2Constraints;
	}

}
