import OrbitComplexity.GroupActions.Actions.OrbitVariety
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Actions.Translations
import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields
import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of algebraic orbits

Translations preserve the smooth locus of an orbit projection. In characteristic zero,
the extension of function fields gives a smooth generic point, and translations then
show that the whole projection is smooth. The orbit variety itself is smooth over an
algebraically closed field by transitivity and density of its smooth locus.

## Main results

* `GroupActions.orbitProjection_smooth`: projections from irreducible groups to their orbits
  are smooth in characteristic zero.
* `GroupActions.orbitVariety_smooth`: orbit varieties over algebraically closed fields are smooth.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

/-- A dominant finite-presentation morphism is smooth at the source generic point in char0. -/
private theorem genericPoint_mem_smoothLocus_zero (K : Type u) [Field K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] (f : X ⟶ Y) [IsDominant f]
    [LocallyOfFinitePresentation f] : genericPoint X ∈ f.smoothLocus := by
  have hyField : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [map_genericPoint f]
    exact Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk (f (genericPoint X))) := hyField.toField
  have : CharZero (Y.presheaf.stalk (f (genericPoint X))) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField


/-- Composing with a codomain isomorphism preserves the smooth locus. -/
private theorem smoothLocus_postIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    [LocallyOfFinitePresentation f] : (f ≫ e.hom).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ e.hom).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  change ((f.stalkMap x).hom.comp (e.hom.stalkMap (f x)).hom).FormallySmooth ↔
    (f.stalkMap x).hom.FormallySmooth
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (e.hom.stalkMap (f x)) (f.stalkMap x)

/-- A commuting pair of isomorphisms preserves the smooth locus of a morphism. -/
private theorem smoothLocus_of_commutingIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ≅ X) (b : Y ≅ Y) (h : a.hom ≫ f = f ≫ b.hom)
    [LocallyOfFinitePresentation f] : a.hom ⁻¹ᵁ f.smoothLocus = f.smoothLocus := by
  calc
    a.hom ⁻¹ᵁ f.smoothLocus = (a.hom ≫ f).smoothLocus :=
      Scheme.Hom.preimage_smoothLocus_eq _ _
    _ = (f ≫ b.hom).smoothLocus := by
      apply TopologicalSpace.Opens.ext
      exact congrArg (fun g : X ⟶ Y => {x | (g.stalkMap x).hom.FormallySmooth}) h
    _ = f.smoothLocus := smoothLocus_postIso _ _


variable {K : Type u} [Field K] [IsAlgClosed K]
  (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]

private theorem projection_points (x : X.points) (a : H.points) :
    Variety.mapPoints (orbitInclusion H X x)
      (Variety.mapPoints (orbitProjection H X x) a) = a • x := by
  rw [← Variety.mapPoints_comp, orbitProjection_fac, Variety.mapPoints_orbitMorphism]

private theorem orbit_stable (x : X.points) (h : H.points)
    (y : (orbitVariety H X x).points) :
    h • Variety.mapPoints (orbitInclusion H X x) y ∈
      Set.range (Variety.mapPoints (orbitInclusion H X x)) := by
  obtain ⟨a, rfl⟩ := orbitProjection_points_surjective H X x y
  refine ⟨Variety.mapPoints (orbitProjection H X x) (h * a), ?_⟩
  rw [projection_points, projection_points, mul_smul]

@[instance_reducible]
private def orbitAction (x : X.points) : ModObj H.toOver (orbitVariety H X x).toOver :=
  Variety.modObjOfInvariant H X (orbitVariety H X x) (orbitInclusion H X x)
    (orbit_stable H X x)

attribute [local instance] orbitAction

private theorem projection_translation (x : X.points) (h : H.points) :
    (leftTranslation H h).hom ≫ orbitProjection H X x =
      orbitProjection H X x ≫ Variety.translateMorphism H (orbitVariety H X x) h := by
  apply Variety.mapPoints_injective
  funext a
  apply Variety.mapPoints_injective_of_mono (orbitInclusion H X x)
  simp only [Variety.mapPoints_comp, leftTranslation_points,
    Variety.mapPoints_translateMorphism]
  rw [projection_points,
    Variety.modObjOfInvariant_smul H X (orbitVariety H X x) (orbitInclusion H X x)
      (orbit_stable H X x), projection_points, mul_smul]

/-- In characteristic zero the projection from an irreducible group to its orbit is smooth. -/
theorem orbitProjection_smooth [CharZero K] [IrreducibleSpace H.scheme] (x : X.points) :
    Smooth (orbitProjection H X x).left := by
  let O := orbitVariety H X x
  let p : H.scheme ⟶ O.scheme := (orbitProjection H X x).left
  have : IsIntegral H.scheme := isIntegral_of_irreducibleSpace_of_isReduced H.scheme
  have : IsIntegral O.scheme := orbitVarietyIntegral H X x
  have : O.scheme.Over (Spec (CommRingCat.of K)) := ⟨O.toSpec⟩
  have : LocallyOfFiniteType p := Variety.locallyOfFiniteType_hom (orbitProjection H X x)
  have : Surjective p := orbitProjection_surjective H X x
  have : IsDominant p := by infer_instance
  have hgen := genericPoint_mem_smoothLocus_zero K p
  have : JacobsonSpace H.scheme := LocallyOfFiniteType.jacobsonSpace H.toSpec
  change Smooth p
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hbad
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints hbad
    p.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints
    (show (p.smoothLocus : Set H.scheme).Nonempty from ⟨genericPoint H.scheme, hgen⟩)
    p.smoothLocus.2.isLocallyClosed
  let pa := H.pointsEquivClosedPoints.symm ⟨a, hac⟩
  let pb := H.pointsEquivClosedPoints.symm ⟨b, hbc⟩
  have hpa : H.pointMap pa = a :=
    congrArg Subtype.val (H.pointsEquivClosedPoints.apply_symm_apply ⟨a, hac⟩)
  have hpb : H.pointMap pb = b :=
    congrArg Subtype.val (H.pointsEquivClosedPoints.apply_symm_apply ⟨b, hbc⟩)
  let h : H.points := pb * pa⁻¹
  let e : H.scheme ≅ H.scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso (leftTranslation H h)
  let t : O.scheme ≅ O.scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso (Variety.translationIso H O h)
  have he : e.hom ≫ p = p ≫ t.hom :=
    congrArg Over.Hom.left (projection_translation H X x h)
  have hab : e.hom a = b := by
    change (leftTranslation H h).hom.left a = b
    have hpoints : Variety.mapPoints (leftTranslation H h).hom pa = pb := by
      rw [leftTranslation_points]
      simp only [h, mul_assoc, inv_mul_cancel, mul_one]
    have hh := congrArg H.pointMap hpoints
    change (leftTranslation H h).hom.left (H.pointMap pa) = H.pointMap pb at hh
    simpa only [hpa, hpb] using hh
  have hpre := smoothLocus_of_commutingIso p e t he
  have hm : a ∈ e.hom ⁻¹ᵁ p.smoothLocus := by
    change e.hom a ∈ p.smoothLocus
    rw [hab]
    exact hb
  rw [hpre] at hm
  exact ha hm

/-- An orbit variety over an algebraically closed field is smooth over that field. -/
theorem orbitVariety_smooth (x : X.points) : Smooth (orbitVariety H X x).toSpec := by
  let O := orbitVariety H X x
  let p := O.toSpec
  have : Nonempty O.scheme :=
    ⟨O.pointMap (Variety.mapPoints (orbitProjection H X x) 1)⟩
  have : JacobsonSpace O.scheme := LocallyOfFiniteType.jacobsonSpace p
  change Smooth p
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hbad
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints hbad
    p.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints
    p.dense_smoothLocus_of_perfectField.nonempty p.smoothLocus.2.isLocallyClosed
  let pa := O.pointsEquivClosedPoints.symm ⟨a, hac⟩
  let pb := O.pointsEquivClosedPoints.symm ⟨b, hbc⟩
  have hpa : O.pointMap pa = a :=
    congrArg Subtype.val (O.pointsEquivClosedPoints.apply_symm_apply ⟨a, hac⟩)
  have hpb : O.pointMap pb = b :=
    congrArg Subtype.val (O.pointsEquivClosedPoints.apply_symm_apply ⟨b, hbc⟩)
  obtain ⟨a', ha'⟩ := orbitProjection_points_surjective H X x pa
  obtain ⟨b', hb'⟩ := orbitProjection_points_surjective H X x pb
  let h : H.points := b' * a'⁻¹
  have hsmul : h • pa = pb := by
    apply Variety.mapPoints_injective_of_mono (orbitInclusion H X x)
    rw [Variety.modObjOfInvariant_smul H X (orbitVariety H X x) (orbitInclusion H X x)
      (orbit_stable H X x), ← ha', projection_points, ← hb', projection_points]
    simp only [h, mul_smul, inv_smul_smul]
  let t := Variety.translationIso H O h
  let e : O.scheme ≅ O.scheme := (Over.forget _).mapIso t
  have he : e.hom ≫ p = p ≫ (Iso.refl _).hom := by
    change t.hom.left ≫ O.toSpec = O.toSpec ≫ 𝟙 _
    rw [Category.comp_id]
    exact t.hom.w
  have hab : e.hom a = b := by
    change t.hom.left a = b
    have hpoints : Variety.mapPoints t.hom pa = pb := by
      change Variety.mapPoints (Variety.translateMorphism H O h) pa = pb
      rw [Variety.mapPoints_translateMorphism]
      exact hsmul
    have hh := congrArg O.pointMap hpoints
    change t.hom.left (O.pointMap pa) = O.pointMap pb at hh
    simpa only [hpa, hpb] using hh
  have hpre := smoothLocus_of_commutingIso p e (Iso.refl _) he
  have hm : a ∈ e.hom ⁻¹ᵁ p.smoothLocus := by
    change e.hom a ∈ p.smoothLocus
    rw [hab]
    exact hb
  rw [hpre] at hm
  exact ha hm


end

end GroupActions
