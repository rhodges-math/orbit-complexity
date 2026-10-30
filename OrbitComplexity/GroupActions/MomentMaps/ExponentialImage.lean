import OrbitComplexity.GroupActions.MomentMaps.Basic
import OrbitComplexity.GroupActions.MomentMaps.PositiveOrbit
import Batteries.Tactic.Lint

/-! # Exponential coordinates and projective moment images

Positive exponential changes of complex coordinates preserve their support.
Their moment values exhaust the intrinsic interior of the supported weight
polytope, and every projective moment value lies in that intrinsic interior.
-/

namespace GroupActions

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Multiplication by a half exponential multiplies norm-square by the full exponential. -/
theorem normSq_mul_exp_half (z : ℂ) (t : ℝ) :
    Complex.normSq (z * (Real.exp (t / 2) : ℂ)) = Complex.normSq z * Real.exp t := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← Real.exp_add, add_halves]

/-- Positive exponential coordinate factors preserve the nonzero coordinates. -/
theorem support_mul_exp_half {I : Type*} (z : I → ℂ) (t : I → ℝ) :
    Function.support (fun i => z i * (Real.exp (t i / 2) : ℂ)) = Function.support z := by
  ext i
  simp [Function.mem_support]

/-- A positive exponential change of coordinates preserves a nonzero vector. -/
theorem mul_exp_half_ne_zero {I : Type*} (z : I → ℂ) (hz : z ≠ 0) (t : I → ℝ) :
    (fun i => z i * (Real.exp (t i / 2) : ℂ)) ≠ 0 := by
  intro hzero
  apply hz
  apply Function.support_eq_empty_iff.mp
  rw [← support_mul_exp_half z t, hzero]
  simp

private theorem centerMass_support {I E : Type*} [Fintype I] [AddCommGroup E]
    [Module ℝ E] (weight : I → E) (a : I → ℝ) (z : I → ℂ)
    (hzero : ∀ i, z i = 0 → a i = 0) :
    Finset.univ.centerMass a weight =
      Finset.univ.centerMass (fun i : Function.support z => a i.val)
        (fun i : Function.support z => weight i.val) := by
  let s := Finset.univ.filter (fun i => z i ≠ 0)
  have hs : ∀ i, i ∈ s ↔ i ∈ Function.support z := by
    intro i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_support]
  calc
    _ = s.centerMass a weight := by
      symm
      apply Finset.centerMass_subset weight (Finset.filter_subset _ _)
      intro i _ hi
      apply hzero i
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
    _ = _ := by
      unfold Finset.centerMass
      rw [Finset.sum_subtype s hs a,
        Finset.sum_subtype s hs (fun i => a i • weight i)]

variable {I E : Type*} [iFintype : Fintype I] [eNorm : NormedAddCommGroup E]
  [eSpace : NormedSpace ℝ E] [eFinite : FiniteDimensional ℝ E]

/-- Every moment value lies in the intrinsic interior of its supported weight polytope. -/
theorem momentMap_mem_intrinsicInterior (weight : I → E)
    (p : Projectivization ℂ (I → ℂ)) :
    momentMap weight p ∈ intrinsicInterior ℝ (weightPolytope weight p) := by
  refine Projectivization.ind ?_ p
  intro z hz
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  let : Nonempty (Function.support z) := ⟨⟨i, hi⟩⟩
  have hcenter := @centerMass_mem_intrinsicInterior (Function.support z) E
    eNorm eSpace inferInstance inferInstance eFinite
    (fun j => weight j.val) (fun j => Complex.normSq (z j.val))
    (fun j => Complex.normSq_pos.mpr j.property)
  rw [momentMap_mk, weightPolytope_mk, Set.image_eq_range]
  rw [centerMass_support weight (fun j => Complex.normSq (z j)) z
    (by intro j hj; rw [hj, Complex.normSq_zero])]
  exact hcenter

/-- Exponential coordinate changes realize every point of the supported intrinsic interior. -/
theorem exists_momentMap_exp_eq (weight : I → E) (z : I → ℂ) (hz : z ≠ 0) (q : E)
    (hq : q ∈ intrinsicInterior ℝ
      (weightPolytope weight (Projectivization.mk ℂ z hz))) :
    ∃ ℓ : E →L[ℝ] ℝ,
      ∃ hnonzero : (fun i => z i * (Real.exp (ℓ (weight i) / 2) : ℂ)) ≠ 0,
        Function.support (fun i => z i * (Real.exp (ℓ (weight i) / 2) : ℂ)) =
          Function.support z ∧
        weightPolytope weight
            (Projectivization.mk ℂ (fun i => z i * (Real.exp (ℓ (weight i) / 2) : ℂ))
              hnonzero) = weightPolytope weight (Projectivization.mk ℂ z hz) ∧
        momentMap weight
          (Projectivization.mk ℂ (fun i => z i * (Real.exp (ℓ (weight i) / 2) : ℂ))
            hnonzero) = q := by
  rw [weightPolytope_mk, Set.image_eq_range] at hq
  have hcenter := @exists_centerMass_exp_eq (Function.support z) E eNorm eSpace
    inferInstance eFinite (fun i => weight i.val) (fun i => Complex.normSq (z i.val))
    (fun i => Complex.normSq_pos.mpr i.property) q hq
  obtain ⟨ℓ, hℓ⟩ := hcenter
  have hnonzero := mul_exp_half_ne_zero z hz (fun i => ℓ (weight i))
  refine ⟨ℓ, hnonzero, support_mul_exp_half z (fun i => ℓ (weight i)), ?_, ?_⟩
  · rw [weightPolytope_mk, weightPolytope_mk, support_mul_exp_half]
  · rw [momentMap_mk]
    simp only [normSq_mul_exp_half]
    rw [centerMass_support weight
      (fun i => Complex.normSq (z i) * Real.exp (ℓ (weight i))) z
      (by intro i hi; rw [hi, Complex.normSq_zero, zero_mul])]
    exact hℓ

end

end GroupActions
