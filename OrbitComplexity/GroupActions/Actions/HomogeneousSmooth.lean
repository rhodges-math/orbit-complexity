import OrbitComplexity.GroupActions.Actions.OrbitSmooth

/-! # Smooth equivariant morphisms from transitive varieties

A dominant equivariant morphism between integral varieties is smooth in characteristic
zero when the group is transitive on rational points of its source. The generic stalk
extension is separable, and translation carries the smooth locus to every closed point.
-/

open CategoryTheory AlgebraicGeometry Topology
namespace GroupActions
noncomputable section
universe u

private theorem generic_smooth (K : Type u) [Field K] [CharZero K]
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

private theorem smooth_postIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z)
    [LocallyOfFinitePresentation f] : (f ≫ e.hom).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ e.hom).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  change ((f.stalkMap x).hom.comp (e.hom.stalkMap (f x)).hom).FormallySmooth ↔
    (f.stalkMap x).hom.FormallySmooth
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (e.hom.stalkMap (f x)) (f.stalkMap x)

private theorem smooth_commutingIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ≅ X) (b : Y ≅ Y) (h : a.hom ≫ f = f ≫ b.hom)
    [LocallyOfFinitePresentation f] : a.hom ⁻¹ᵁ f.smoothLocus = f.smoothLocus := by
  calc
    a.hom ⁻¹ᵁ f.smoothLocus = (a.hom ≫ f).smoothLocus :=
      Scheme.Hom.preimage_smoothLocus_eq _ _
    _ = (f ≫ b.hom).smoothLocus := by
      apply TopologicalSpace.Opens.ext
      exact congrArg (fun g : X ⟶ Y => {x | (g.stalkMap x).hom.FormallySmooth}) h
    _ = f.smoothLocus := smooth_postIso _ _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (H X Y : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

omit [CharZero K] in
private theorem equivariant_translation (f : X.toOver ⟶ Y.toOver)
    [IsModHom H.toOver f] (h : H.points) :
    (Variety.translationIso H X h).hom ≫ f =
      f ≫ (Variety.translationIso H Y h).hom := by
  apply Variety.mapPoints_injective
  funext x
  simp only [Variety.mapPoints_comp]
  change Variety.mapPoints f
      (Variety.mapPoints (Variety.translateMorphism H X h) x) =
    Variety.mapPoints (Variety.translateMorphism H Y h) (Variety.mapPoints f x)
  simp only [Variety.mapPoints_translateMorphism]
  exact equivariant_points H X Y f h x

/-- A dominant equivariant morphism from a transitive integral variety is smooth in char0. -/
theorem smooth_of_transitive [IsIntegral X.scheme] [IsIntegral Y.scheme]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] [IsDominant f.left]
    (htrans : ∀ a b : X.points, ∃ h : H.points, h • a = b) : Smooth f.left := by
  let p : X.scheme ⟶ Y.scheme := f.left
  have : Y.scheme.Over (Spec (CommRingCat.of K)) := ⟨Y.toSpec⟩
  have : LocallyOfFiniteType p := Variety.locallyOfFiniteType_hom f
  have hgen := generic_smooth K p
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  change Smooth p
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hbad
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints hbad
    p.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints
    (show (p.smoothLocus : Set X.scheme).Nonempty from ⟨genericPoint X.scheme, hgen⟩)
    p.smoothLocus.2.isLocallyClosed
  let pa := X.pointsEquivClosedPoints.symm ⟨a, hac⟩
  let pb := X.pointsEquivClosedPoints.symm ⟨b, hbc⟩
  have hpa : X.pointMap pa = a :=
    congrArg Subtype.val (X.pointsEquivClosedPoints.apply_symm_apply ⟨a, hac⟩)
  have hpb : X.pointMap pb = b :=
    congrArg Subtype.val (X.pointsEquivClosedPoints.apply_symm_apply ⟨b, hbc⟩)
  obtain ⟨h, hsmul⟩ := htrans pa pb
  let e : X.scheme ≅ X.scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso (Variety.translationIso H X h)
  let t : Y.scheme ≅ Y.scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso (Variety.translationIso H Y h)
  have he : e.hom ≫ p = p ≫ t.hom :=
    congrArg Over.Hom.left (equivariant_translation H X Y f h)
  have hab : e.hom a = b := by
    have hpoints : Variety.mapPoints (Variety.translationIso H X h).hom pa = pb := by
      change Variety.mapPoints (Variety.translateMorphism H X h) pa = pb
      rw [Variety.mapPoints_translateMorphism]
      exact hsmul
    have hh := congrArg X.pointMap hpoints
    change e.hom (X.pointMap pa) = X.pointMap pb at hh
    simpa only [hpa, hpb] using hh
  have hpre := smooth_commutingIso p e t he
  have hm : a ∈ e.hom ⁻¹ᵁ p.smoothLocus := by
    change e.hom a ∈ p.smoothLocus
    rw [hab]
    exact hb
  rw [hpre] at hm
  exact ha hm

end
end GroupActions
