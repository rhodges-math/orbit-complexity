import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
import Batteries.Tactic.Lint

/-! # Morphisms on prescribed arithmetic models

A morphism between two field fibres descends between scalar extensions of
their prescribed models. Both field comparisons retain their projections
to the earlier models.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

private theorem scalar_original
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion i.property.2).toRingHom)) a =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) a := by
  change pullback.lift _ _ _ ≫ pullback.snd _ a = _
  exact pullback.lift_snd _ _ _

private theorem iso_conjugate {B : Scheme.{u}} {X Y X' Y' : Over B}
    (E : X ≅ X') (F : Y ≅ Y') (g : X ⟶ Y) :
    E.hom.left ≫ (E.inv ≫ g ≫ F.hom).left = g.left ≫ F.hom.left := by
  exact congrArg Over.Hom.left (show E.hom ≫ (E.inv ≫ g ≫ F.hom) = g ≫ F.hom
    from by simp)

/-- A morphism between the field fibres of two prescribed models descends
to one coefficient stage, retaining both Cartesian comparisons and both
projections to the prescribed models. -/
theorem exists_arrow_model_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C D : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation D.hom]
    (X Y : Over (Spec (.of K))) (g : X ⟶ Y)
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    ∃ (i : CoefficientStage S)
      (f : stageScalarModel S C.hom i ⟶ stageScalarModel S D.hom i)
      (rC : X.left ⟶ (stageScalarModel S C.hom i).left)
      (rD : Y.left ⟶ (stageScalarModel S D.hom i).left),
      IsPullback rC X.hom (stageScalarModel S C.hom i).hom
        (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) ∧
      IsPullback rD Y.hom (stageScalarModel S D.hom i).hom
        (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) ∧
      rC ≫ pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion i.property.2).toRingHom)) C.hom = qC ∧
      rD ≫ pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion i.property.2).toRingHom)) D.hom = qD ∧
      rC ≫ f.left = g.left ≫ rD := by
  let EC : X ≅ genericScalarModel S C.hom := hC.flip.isoOverPullback
  let ED : Y ≅ genericScalarModel S D.hom := hD.flip.isoOverPullback
  let gK : genericScalarModel S C.hom ⟶ genericScalarModel S D.hom :=
    EC.inv ≫ g ≫ ED.hom
  obtain ⟨i, f, hf⟩ := exists_model_morphism S hS C.hom D.hom gK
  let rC : X.left ⟶ (stageScalarModel S C.hom i).left :=
    EC.hom.left ≫ (modelScalarCone S C.hom).π.app (op i)
  let rD : Y.left ⟶ (stageScalarModel S D.hom i).left :=
    ED.hom.left ≫ (modelScalarCone S D.hom).π.app (op i)
  refine ⟨i, f, rC, rD, overIso_modelStage_cartesian S C.hom i X EC,
    overIso_modelStage_cartesian S D.hom i Y ED, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => EC.hom.left ≫ k) (scalar_original S C.hom i)).trans
        hC.flip.isoOverPullback_hom_left_comp_snd)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ED.hom.left ≫ k) (scalar_original S D.hom i)).trans
        hD.flip.isoOverPullback_hom_left_comp_snd)
  · have hfield :
        (modelScalarCone S C.hom).π.app (op i) ≫ f.left =
          gK.left ≫ (modelScalarCone S D.hom).π.app (op i) := hf
    have hpre :
        EC.hom.left ≫ ((modelScalarCone S C.hom).π.app (op i) ≫ f.left) =
          EC.hom.left ≫ (gK.left ≫ (modelScalarCone S D.hom).π.app (op i)) :=
      congrArg (fun k : (genericScalarModel S C.hom).left ⟶
        (stageScalarModel S D.hom i).left => EC.hom.left ≫ k) hfield
    change (EC.hom.left ≫ (modelScalarCone S C.hom).π.app (op i)) ≫ f.left =
      g.left ≫ (ED.hom.left ≫ (modelScalarCone S D.hom).π.app (op i))
    exact (Category.assoc _ _ _).trans (hpre.trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : X.left ⟶ (genericScalarModel S D.hom).left =>
          k ≫ (modelScalarCone S D.hom).π.app (op i)) (iso_conjugate EC ED g))).trans
        (Category.assoc _ _ _)))

end FrobeniusSplitting
