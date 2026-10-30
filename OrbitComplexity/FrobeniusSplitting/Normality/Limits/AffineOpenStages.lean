import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Data.Finset.Order
import Batteries.Tactic.Lint

/-! # Affine opens at coefficient stages

A finite family of affine opens in generic scalar models descends to one
coefficient stage above any prescribed stage, with its inverse-image equations.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

private theorem preimage_transition {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) (U : (stageScalarModel S a i).left.Opens) :
    (modelScalarCone S a).π.app (op j) ⁻¹ᵁ (stageScalarTransition S a hij ⁻¹ᵁ U) =
      (modelScalarCone S a).π.app (op i) ⁻¹ᵁ U := by
  exact (Scheme.Hom.comp_preimage ((modelScalarCone S a).π.app (op j))
    (stageScalarTransition S a hij) U).symm.trans
    (congrArg (fun f => f ⁻¹ᵁ U) ((modelScalarCone S a).w (homOfLE hij).op))

/-- A finite family of affine generic opens has affine models at a common
coefficient stage above any prescribed stage, with the same scalar preimages. -/
theorem exists_affine_opens_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type u} [Finite I]
    (X : I → Over (Spec (.of S)))
    [∀ i, QuasiSeparatedSpace (X i).left]
    (U : ∀ i, (genericScalarModel S (X i).hom).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (V : ∀ i, (stageScalarModel S (X i).hom t).left.Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      ∀ i, (modelScalarCone S (X i).hom).π.app (op t) ⁻¹ᵁ V i = U i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  have hexists (i : I) : ∃ (t : CoefficientStage S)
      (V : (stageScalarModel S (X i).hom t).left.Opens),
      IsAffineOpen V ∧ (modelScalarCone S (X i).hom).π.app (op t) ⁻¹ᵁ V = U i := by
    obtain ⟨j, V, hV, hj⟩ := exists_isAffineOpen_preimage_eq
      (D := modelScalarStages S (X i).hom) (c := modelScalarCone S (X i).hom)
      (hc := modelScalarLimit S hS (X i).hom) (U i) (hU i)
    exact ⟨j.unop, V, hV, hj⟩
  choose k W hW hk using hexists
  obtain ⟨t, ht⟩ := Finset.exists_le (insert start (Finset.univ.image k))
  have hstart : start ≤ t := ht start (Finset.mem_insert_self _ _)
  have hkt (i : I) : k i ≤ t :=
    ht (k i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem k (Finset.mem_univ i)))
  let V (i : I) := stageScalarTransition S (X i).hom (hkt i) ⁻¹ᵁ W i
  refine ⟨t, hstart, V, ?_, ?_⟩
  · intro i
    let : IsAffineHom (stageScalarTransition S (X i).hom (hkt i)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (stageScalarCartesian S (X i).hom (hkt i)).flip inferInstance
    exact (hW i).preimage _
  · intro i
    exact (preimage_transition S (X i).hom (hkt i) (W i)).trans (hk i)

end FrobeniusSplitting
