import OrbitComplexity.GroupActions.Tori.MonomialMaps

/-! # Weight maps on coordinate supports

Multiplying weight coordinates by nonzero scalars leaves their generated algebra unchanged.
Zero coordinates contribute no generators. The image dimension is therefore the rank of the
weights on the support, also expressed as a real span dimension.

## Main definitions

* `GroupActions.weightedPolynomialMap`: the monomial map with prescribed coordinate scalars.

## Main results

* `GroupActions.ringKrullDim_weightedImage`: dimension in terms of the integral support lattice.
* `GroupActions.ringKrullDim_weighted_real`: dimension in terms of the real character span.
-/

namespace GroupActions

noncomputable section

open Multiplicative

universe u

private theorem adjoin_scaled_coordinates {K A ι : Type u} [Field K] [CommRing A] [Algebra K A]
    (v : ι → A) (x : ι → K) :
    Algebra.adjoin K (Set.range (fun i ↦ x i • v i)) =
      Algebra.adjoin K (Set.range (fun i : {i // x i ≠ 0} ↦ v i.val)) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    by_cases hi : x i = 0
    · simp only [hi, zero_smul]
      exact zero_mem _
    · have hv : v i ∈ Algebra.adjoin K
          (Set.range (fun j : {i // x i ≠ 0} ↦ v j.val)) :=
        Algebra.subset_adjoin ⟨⟨i, hi⟩, rfl⟩
      exact (Algebra.adjoin K _).smul_mem hv _
  · apply Algebra.adjoin_le
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    have h := (Algebra.adjoin K (Set.range (fun i ↦ x i • v i))).smul_mem
      (Algebra.subset_adjoin ⟨i, rfl⟩) (x i)⁻¹
    change v i ∈ Algebra.adjoin K (Set.range (fun i ↦ x i • v i))
    simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using h


variable {K ι M : Type u} [Field K] [Fintype ι] [AddCommGroup M]

private theorem weightPolynomialMap_eq_aeval (w : ι → M) :
    weightPolynomialMap (K := K) w =
      MvPolynomial.aeval (fun i ↦ MonoidAlgebra.single (ofAdd (w i)) (1 : K)) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [weightPolynomialMap_X, MvPolynomial.aeval_X]

/-- The polynomial map sends a variable to its weight monomial scaled by its coordinate. -/
def weightedPolynomialMap (w : ι → M) (x : ι → K) :
    MvPolynomial ι K →ₐ[K] MonoidAlgebra K (Multiplicative M) :=
  MvPolynomial.aeval (fun i ↦ x i • MonoidAlgebra.single (ofAdd (w i)) 1)

/-- The image dimension is the integral rank of the weights at nonzero coordinates. -/
theorem ringKrullDim_weightedImage [Module.Free ℤ M] [Module.Finite ℤ M] (w : ι → M) (x : ι → K) :
    ringKrullDim (weightedPolynomialMap w x).range =
      (Module.finrank ℤ (Submodule.span ℤ
        (Set.range (fun i : {i // x i ≠ 0} ↦ w i.val))) : WithBot ℕ∞) := by
  classical
  rw [weightedPolynomialMap, MvPolynomial.aeval_range, adjoin_scaled_coordinates,
    ← MvPolynomial.aeval_range, ← weightPolynomialMap_eq_aeval]
  exact ringKrullDim_weightImage _

omit [Fintype ι] in
/-- Each variable maps to its scaled weight monomial. -/
theorem weightedPolynomialMap_X (w : ι → M) (x : ι → K) (i : ι) :
    weightedPolynomialMap w x (MvPolynomial.X i) =
      x i • MonoidAlgebra.single (ofAdd (w i)) 1 :=
  MvPolynomial.aeval_X _ _

/-- The image dimension equals the real dimension of the supported integer weight span. -/
theorem ringKrullDim_weighted_real {κ : Type u} [Finite κ]
    (w : ι → κ →₀ ℤ) (x : ι → K) :
    ringKrullDim (weightedPolynomialMap w x).range =
      (Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun (i : {i // x i ≠ 0}) k ↦ (w i.val k : ℝ)))) : WithBot ℕ∞) := by
  rw [ringKrullDim_weightedImage, finrank_realSpan_finsupp]

end

end GroupActions
