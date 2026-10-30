import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.AffineStages

/-! # A common affine stage for a finite family

Affineness of finitely many generic scalar models holds simultaneously
at one coefficient stage above any prescribed threshold.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u v

private theorem affine_stage_of_le
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of S))) {i j : CoefficientStage S} (hij : i ≤ j)
    (hi : IsAffine (stageScalarModel S X.hom i).left) :
    IsAffine (stageScalarModel S X.hom j).left := by
  let : IsAffine ((modelScalarStages S X.hom).obj (op i)) := hi
  let f : op j ⟶ op i := (homOfLE hij).op
  have hj : IsAffine ((modelScalarStages S X.hom).obj (op j)) :=
    isAffine_of_isAffineHom ((modelScalarStages S X.hom).map f)
  exact hj

/-- A finite family of affine generic scalar models becomes affine at one
coefficient stage above any prescribed threshold. -/
theorem exists_affine_family_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I] (X : I → Over (Spec (.of S)))
    [∀ i, CompactSpace (X i).left] [∀ i, QuasiSeparatedSpace (X i).left]
    [∀ i, IsAffine (genericScalarModel S (X i).hom).left]
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S), start ≤ j ∧
      ∀ i, IsAffine (stageScalarModel S (X i).hom j).left := by
  classical
  let : Nonempty (CoefficientStage S) := ⟨start⟩
  choose k hk ha using fun i => exists_affine_scalar_stage S hS (X i) start
  obtain ⟨j, hj⟩ := (Set.finite_range k).bddAbove
  obtain ⟨t, hstart, hjt⟩ := exists_ge_ge start j
  refine ⟨t, hstart, fun i => ?_⟩
  exact affine_stage_of_le S (X i) ((hj (Set.mem_range_self i)).trans hjt) (ha i)

end FrobeniusSplitting
