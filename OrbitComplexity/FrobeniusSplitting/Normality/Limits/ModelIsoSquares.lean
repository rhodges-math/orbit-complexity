import OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedIsoStages
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Isomorphisms preserving arrows at a coefficient stage -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

open private extendStageIso iso_old_base retain_iso_triangle from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedIsoStages
open private scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private transition_comp from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoDescent

private theorem comp_agreement {C : Type*} [Category C] {A B D Z : C}
    (u : A ⟶ B) (v : B ⟶ D) (w : A ⟶ D) (f g : D ⟶ Z)
    (hw : u ≫ v = w) (h : v ≫ f = v ≫ g) : w ≫ f = w ≫ g := by
  calc
    _ = (u ≫ v) ≫ f := by rw [hw]
    _ = u ≫ (v ≫ f) := Category.assoc _ _ _
    _ = u ≫ (v ≫ g) := by rw [h]
    _ = (u ≫ v) ≫ g := (Category.assoc _ _ _).symm
    _ = _ := by rw [hw]

private def underlyingIso {C : Type*} [Category C] {B : C} {X Y : Over B}
    (E : X ≅ Y) : X.left ≅ Y.left where
  hom := E.hom.left
  inv := E.inv.left
  hom_inv_id := congrArg (fun f : X ⟶ X => f.left) E.hom_inv_id
  inv_hom_id := congrArg (fun f : Y ⟶ Y => f.left) E.inv_hom_id

private theorem closed_iso {B : Scheme.{u}} {X Y Z : Over B}
    (i : X ⟶ Z) (j : Y ⟶ Z) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (h : i.left.ker = j.left.ker) : ∃ E : X ≅ Y, E.hom ≫ j = i := by
  let f : X.left ⟶ Y.left := IsClosedImmersion.lift j.left i.left h.symm.le
  have hf : f ≫ j.left = i.left := IsClosedImmersion.lift_fac _ _ _
  let : IsIso f := IsClosedImmersion.isIso_lift j.left i.left h.symm
  have hb : f ≫ Y.hom = X.hom := by
    calc
      _ = f ≫ (j.left ≫ Z.hom) := by rw [j.w]
      _ = (f ≫ j.left) ≫ Z.hom := (Category.assoc _ _ _).symm
      _ = i.left ≫ Z.hom := by rw [hf]
      _ = _ := i.w
  refine ⟨Over.isoMk (asIso f) hb, ?_⟩
  apply CostructuredArrow.hom_ext
  exact hf

private theorem iso_triangle {C : Type*} [Category C]
    {X Y Z X' Y' Z' : C} (E : X ≅ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (qX : X ⟶ X') (qY : Y ⟶ Y') (qZ : Z ⟶ Z')
    (i' : X' ⟶ Z') (j' : Y' ⟶ Z')
    (hE : E.hom ≫ j = i) (hi : i ≫ qZ = qX ≫ i')
    (hj : j ≫ qZ = qY ≫ j') : E.hom ≫ qY ≫ j' = qX ≫ i' := by
  calc
    _ = E.hom ≫ (j ≫ qZ) := by rw [hj]
    _ = (E.hom ≫ j) ≫ qZ := (Category.assoc _ _ _).symm
    _ = i ≫ qZ := by rw [hE]
    _ = _ := hi

private def modelComparison {B T : Scheme.{u}} (κ : T ⟶ B)
    (M : Over B) {X : Over T} (q : X.left ⟶ M.left)
    (h : IsPullback q X.hom M.hom κ) :
    X ≅ Over.mk (pullback.fst κ M.hom) :=
  Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_fst

private theorem modelComparison_projection {B T : Scheme.{u}} (κ : T ⟶ B)
    (M : Over B) {X : Over T} (q : X.left ⟶ M.left)
    (h : IsPullback q X.hom M.hom κ) :
    (modelComparison κ M q h).hom.left ≫ pullback.snd κ M.hom = q :=
  h.flip.isoPullback_hom_snd

private theorem conjugate_triangle {C : Type*} [Category C]
    {X Y A B D E Z F : C} (α : X ≅ A) (β : Y ≅ B) (e : X ≅ Y)
    (qX : X ⟶ D) (qY : Y ⟶ E) (a : A ⟶ D) (b : B ⟶ E)
    (f : D ⟶ F) (g : E ⟶ F) (i : X ⟶ Z) (j : Y ⟶ Z) (qZ : Z ⟶ F)
    (hα : α.hom ≫ a = qX) (hβ : β.hom ≫ b = qY)
    (he : e.hom ≫ j = i) (hf : i ≫ qZ = qX ≫ f) (hg : j ≫ qZ = qY ≫ g) :
    (α.symm ≪≫ e ≪≫ β).hom ≫ b ≫ g = a ≫ f := by
  have h := iso_triangle e i j qX qY qZ f g he hf hg
  calc
    _ = α.inv ≫ (e.hom ≫ ((β.hom ≫ b) ≫ g)) := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = α.inv ≫ (e.hom ≫ (qY ≫ g)) := by rw [hβ]
    _ = α.inv ≫ (qX ≫ f) := congrArg (fun k => α.inv ≫ k) h
    _ = α.inv ≫ ((α.hom ≫ a) ≫ f) := by rw [hα]
    _ = _ := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem triangle_agreement {C : Type*} [Category C]
    {A B A' B' X Y Z : C} (e : A ≅ B) (e' : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (qX : A' ⟶ X) (qY : B' ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (he : u ≫ e'.hom = e.hom ≫ v) (hu : u ≫ qX = a) (hv : v ≫ qY = b)
    (h : e.hom ≫ b ≫ g = a ≫ f) :
    u ≫ (e'.hom ≫ qY ≫ g) = u ≫ (qX ≫ f) := by
  calc
    _ = (u ≫ e'.hom) ≫ qY ≫ g := by simp only [Category.assoc]
    _ = (e.hom ≫ v) ≫ qY ≫ g := by rw [he]
    _ = e.hom ≫ (v ≫ qY) ≫ g := by simp only [Category.assoc]
    _ = e.hom ≫ b ≫ g := by rw [hv]
    _ = a ≫ f := h
    _ = (u ≫ qX) ≫ f := by rw [hu]
    _ = _ := Category.assoc _ _ _

/-- An isomorphism of scalar fibres commuting with arrows to a fixed model
descends above any prescribed coefficient stage with that commutation equation. -/
theorem exists_model_iso_commuting
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [LocallyOfFiniteType F.hom] (i : C ⟶ F) (j : D ⟶ F)
    (E : genericScalarModel S C.hom ≅ genericScalarModel S D.hom)
    (hE : E.hom.left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom ≫ j.left =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom ≫ i.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (Et : stageScalarModel S C.hom t ≅ stageScalarModel S D.hom t),
      Et.hom.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left := by
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  obtain ⟨r, Er, hEr, _⟩ := exists_model_iso S hS C.hom D.hom E
  let qC : (stageScalarModel S C.hom r).left ⟶ C.left := pullback.snd _ C.hom
  let qD : (stageScalarModel S D.hom r).left ⟶ D.left := pullback.snd _ D.hom
  let f : (modelScalarStages S C.hom).obj (op r) ⟶ F.left :=
    Er.hom.left ≫ qD ≫ j.left
  let g : (modelScalarStages S C.hom).obj (op r) ⟶ F.left := qC ≫ i.left
  have hf : f ≫ F.hom = (modelScalarBase S C.hom).app (op r) := by
    change (Er.hom.left ≫ qD ≫ j.left) ≫ F.hom = qC ≫ C.hom
    simpa only [Category.assoc, j.w] using
      iso_old_base
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom))
        C.hom D.hom Er qC qD pullback.condition.symm pullback.condition.symm
  have hg : g ≫ F.hom = (modelScalarBase S C.hom).app (op r) := by
    change (qC ≫ i.left) ≫ F.hom = qC ≫ C.hom
    rw [Category.assoc, i.w]
  have hfg : (modelScalarCone S C.hom).π.app (op r) ≫ f =
      (modelScalarCone S C.hom).π.app (op r) ≫ g := by
    exact triangle_agreement ((Over.forget _).mapIso E) ((Over.forget _).mapIso Er)
      ((modelScalarCone S C.hom).π.app (op r))
      ((modelScalarCone S D.hom).π.app (op r)) qC qD
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
      i.left j.left hEr (scalarLeg_snd S C.hom r) (scalarLeg_snd S D.hom r) hE
  obtain ⟨s, hrs, hs⟩ := exists_scalar_equality S hS C.hom F.hom r f g hf hg hfg
  change stageScalarTransition S C.hom hrs ≫ f =
    stageScalarTransition S C.hom hrs ≫ g at hs
  obtain ⟨t, hst, hstart⟩ := exists_ge_ge s start
  let hrt : r ≤ t := hrs.trans hst
  let Et : stageScalarModel S C.hom t ≅ stageScalarModel S D.hom t :=
    extendStageIso S C.hom D.hom hrt Er
  have ht : stageScalarTransition S C.hom hrt ≫ f =
      stageScalarTransition S C.hom hrt ≫ g := by
    exact comp_agreement (stageScalarTransition S C.hom hst)
      (stageScalarTransition S C.hom hrs) (stageScalarTransition S C.hom hrt) f g
      (transition_comp S C.hom hrs hst) hs
  refine ⟨t, hstart, Et, ?_⟩
  apply retain_iso_triangle (underlyingIso Er) (underlyingIso Et)
    (stageScalarTransition S C.hom hrt) (stageScalarTransition S D.hom hrt)
    (qC ≫ i.left) (qD ≫ j.left)
    (pullback.snd _ C.hom ≫ i.left) (pullback.snd _ D.hom ≫ j.left)
  · exact extendModelMorphism_transition S C.hom D.hom hrt Er.hom
  · rw [← Category.assoc, stageScalarTransition_snd]
  · rw [← Category.assoc, stageScalarTransition_snd]
  · change stageScalarTransition S C.hom hrt ≫ Er.hom.left ≫ qD ≫ j.left =
      stageScalarTransition S C.hom hrt ≫ qC ≫ i.left
    simp only [f, g] at ht
    exact ht

/-- Equality of closed ideals on the scalar fibre yields an isomorphism of the
same closed models commuting over their ambient model at a coefficient stage. -/
theorem exists_closed_ideal_iso_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation D.hom]
    [LocallyOfFiniteType F.hom] (i : C ⟶ F) (j : D ⟶ F)
    (X Y Z : Over (Spec (.of K))) (iK : X ⟶ Z) (jK : Y ⟶ Z)
    [IsClosedImmersion iK.left] [IsClosedImmersion jK.left]
    (qX : X.left ⟶ C.left) (qY : Y.left ⟶ D.left) (qZ : Z.left ⟶ F.left)
    (hX : IsPullback qX X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hi : iK.left ≫ qZ = qX ≫ i.left) (hj : jK.left ≫ qZ = qY ≫ j.left)
    (hker : iK.left.ker = jK.left.ker) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (Et : stageScalarModel S C.hom t ≅ stageScalarModel S D.hom t),
      Et.hom.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          D.hom ≫ j.left =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          C.hom ≫ i.left := by
  obtain ⟨E, hE⟩ := closed_iso iK jK hker
  have hE' : E.hom.left ≫ jK.left = iK.left :=
    congrArg (fun f => f.left) hE
  let α : X ≅ genericScalarModel S C.hom := modelComparison _ C qX hX
  let β : Y ≅ genericScalarModel S D.hom := modelComparison _ D qY hY
  let Em : genericScalarModel S C.hom ≅ genericScalarModel S D.hom :=
    α.symm ≪≫ E ≪≫ β
  apply exists_model_iso_commuting S hS C D F i j Em
  exact conjugate_triangle (underlyingIso α) (underlyingIso β) (underlyingIso E)
    qX qY
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
    i.left j.left iK.left jK.left qZ
    (modelComparison_projection _ C qX hX) (modelComparison_projection _ D qY hY)
    hE' hi hj

end FrobeniusSplitting
