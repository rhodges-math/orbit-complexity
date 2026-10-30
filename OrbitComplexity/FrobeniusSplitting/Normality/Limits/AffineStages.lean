import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Affine scalar models above a prescribed coefficient stage

An affine generic scalar model is the limit of its coefficient models.
Affineness occurs at one stage and persists along the affine transition
morphisms, so that stage may be chosen above any prescribed threshold.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

/-- An affine generic scalar model has an affine coefficient model above
any prescribed coefficient stage. -/
theorem exists_affine_scalar_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (X : Over (Spec (.of S))) [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [IsAffine (genericScalarModel S X.hom).left] (start : CoefficientStage S) :
    ∃ (i : CoefficientStage S), start ≤ i ∧ IsAffine (stageScalarModel S X.hom i).left := by
  let : Nonempty (CoefficientStage S) := ⟨start⟩
  let : IsAffine (modelScalarCone S X.hom).pt := by
    change IsAffine (genericScalarModel S X.hom).left
    infer_instance
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit
    (modelScalarStages S X.hom) (modelScalarCone S X.hom) (modelScalarLimit S hS X.hom)
  obtain ⟨j, hstart, hij⟩ := exists_ge_ge start i.unop
  let : IsAffine ((modelScalarStages S X.hom).obj i) := hi
  let f : op j ⟶ i := (homOfLE hij).op
  let : IsAffineHom ((modelScalarStages S X.hom).map f) := inferInstance
  have hj : IsAffine ((modelScalarStages S X.hom).obj (op j)) :=
    isAffine_of_isAffineHom ((modelScalarStages S X.hom).map f)
  exact ⟨j, hstart, hj⟩

end FrobeniusSplitting
