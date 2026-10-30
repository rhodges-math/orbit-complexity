import OrbitComplexity.BruhatIntervals.Realizations.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The geometric representation of a Coxeter system

The simple geometric reflections satisfy every Coxeter relation. Consequently, the free real
vector space on the simple indices is a realization of each Coxeter system.

## Main definitions

* `geometricAction`: the action of a Coxeter group on its geometric space.
* `geometricRealization`: a realization on the free real vector space on the simple indices.

## Main results

* `geometricReflection_relation`: each product of simple reflections satisfies its Coxeter relation.
* `geometricAction_simple`: each simple generator acts by its geometric reflection.
* `geometricRealization_spec`: the simple roots, form, and action of the geometric realization.

## Implementation notes

Reflection powers are evaluated through rescaled Chebyshev polynomials. The vanishing factors
for even and odd Coxeter exponents follow from their sine evaluation formulas.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals

open Polynomial.Chebyshev

private theorem chebyshev_s_pi_div (k : ℕ) (hk : 2 ≤ k) :
    (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (Real.pi / k)) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hθpos : 0 < Real.pi / k := div_pos Real.pi_pos hkpos
  have hθlt : Real.pi / k < Real.pi := by
    apply (div_lt_iff₀ hkpos).mpr
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi / k) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne'
  have heval := S_two_mul_real_cos (Real.pi / k) ((k : ℤ) - 1)
  have hangle : ((((k : ℤ) - 1 : ℤ) : ℝ) + 1) * (Real.pi / k) = Real.pi := by
    push_cast
    field_simp
    ring
  rw [hangle, Real.sin_pi] at heval
  exact (mul_eq_zero.mp heval).resolve_right hsin

private theorem chebyshev_s_two_pi_div_sum (k : ℕ) (hk : 1 ≤ k) :
    (S ℝ (k : ℤ)).eval (2 * Real.cos (2 * Real.pi / (2 * k + 1))) +
      (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (2 * k + 1))) = 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  have hθpos : 0 < 2 * Real.pi / (2 * k + 1) := div_pos (by positivity) hden
  have hθlt : 2 * Real.pi / (2 * k + 1) < Real.pi := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (2 * Real.pi / (2 * k + 1)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne'
  have heval := S_two_mul_real_cos (2 * Real.pi / (2 * k + 1)) (k : ℤ)
  have heval' := S_two_mul_real_cos (2 * Real.pi / (2 * k + 1)) ((k : ℤ) - 1)
  have hangle : (((k : ℤ) : ℝ) + 1) * (2 * Real.pi / (2 * k + 1)) =
      2 * Real.pi - ((((k : ℤ) - 1 : ℤ) : ℝ) + 1) *
        (2 * Real.pi / (2 * k + 1)) := by
    push_cast
    field_simp
    ring
  rw [hangle, Real.sin_two_pi_sub, ← heval'] at heval
  apply (mul_eq_zero.mp (show
    ((S ℝ (k : ℤ)).eval (2 * Real.cos (2 * Real.pi / (2 * k + 1))) +
      (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (2 * k + 1)))) *
        Real.sin (2 * Real.pi / (2 * k + 1)) = 0 by
    rw [add_mul, heval]
    ring)).resolve_right hsin

variable {Index : Type*} (matrix : CoxeterMatrix Index)

private theorem geometric_pair_pow_of_three_le (i j : Index) (hm : 3 ≤ matrix i j) :
    (geometricReflection matrix i * geometricReflection matrix j) ^ matrix i j = 1 := by
  have hproduct : geometricCoroot matrix i (geometricRoot j) *
        geometricCoroot matrix j (geometricRoot i) - 2 =
      2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)) := by
    rw [geometricCoroot_root, geometricCoroot_root, matrix.symmetric j i]
    rw [show 2 * Real.pi / (matrix i j : ℝ) =
      2 * (Real.pi / (matrix i j : ℝ)) by ring, Real.cos_two_mul]
    ring
  apply LinearEquiv.ext
  intro x
  change ((Module.reflection (geometricCoroot_root_self matrix i) *
    Module.reflection (geometricCoroot_root_self matrix j)) ^ matrix i j) x = x
  rw [Module.reflection_mul_reflection_pow_apply
    (geometricCoroot_root_self matrix i) (geometricCoroot_root_self matrix j)
    (matrix i j) x (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ))) hproduct.symm]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (matrix i j)
  · have hk2 : 2 ≤ k := by omega
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hangle : 2 * Real.pi / ((2 * k : ℕ) : ℝ) = Real.pi / k := by
      push_cast
      field_simp
    have hiA : ((((2 * k : ℕ) : ℤ) - 2) / 2) = (k : ℤ) - 1 := by omega
    have hiB : ((((2 * k : ℕ) : ℤ) - 1) / 2) = (k : ℤ) - 1 := by omega
    rw [hk, hangle, hiA, hiB, chebyshev_s_pi_div k hk2]
    simp only [zero_mul, zero_smul, add_zero]
  · have hk1 : 1 ≤ k := by omega
    have hiA : ((((2 * k + 1 : ℕ) : ℤ) - 2) / 2) = (k : ℤ) - 1 := by omega
    have hiB : ((((2 * k + 1 : ℕ) : ℤ) - 1) / 2) = (k : ℤ) := by omega
    have hiC : ((((2 * k + 1 : ℕ) : ℤ) - 3) / 2) = (k : ℤ) - 1 := by omega
    have hiD : (((2 * k + 1 : ℕ) : ℤ) / 2) = (k : ℤ) := by omega
    rw [hk, hiA, hiB, hiC, hiD]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [chebyshev_s_two_pi_div_sum k hk1]
    simp only [mul_zero, zero_smul, add_zero]

/-- The simple geometric reflections satisfy the Coxeter relation at every pair of indices. -/
theorem geometricReflection_relation (i j : Index) :
    (geometricReflection matrix i * geometricReflection matrix j) ^ matrix i j = 1 := by
  by_cases hzero : matrix i j = 0
  · rw [hzero, pow_zero]
  by_cases hone : matrix i j = 1
  · have hij : i = j := by
      by_contra hne
      exact matrix.off_diagonal i j hne hone
    subst j
    rw [matrix.diagonal, pow_one, ← pow_two, geometricReflection_sq]
  by_cases htwo : matrix i j = 2
  · rw [htwo, (geometricReflection_commute matrix htwo).mul_pow,
      geometricReflection_sq, geometricReflection_sq, mul_one]
  exact geometric_pair_pow_of_three_le matrix i j (by omega)

variable {W : Type*} [Group W] (cs : CoxeterSystem matrix W)

/-- The geometric action of a Coxeter group on the free real vector space on its simple indices. -/
noncomputable def geometricAction : W →* ((Index →₀ ℝ) ≃ₗ[ℝ] (Index →₀ ℝ)) :=
  cs.lift ⟨geometricReflection matrix, geometricReflection_relation matrix⟩

/-- Each simple generator acts by the corresponding simple geometric reflection. -/
theorem geometricAction_simple (i : Index) :
    geometricAction matrix cs (cs.simple i) = geometricReflection matrix i :=
  cs.lift_apply_simple (geometricReflection_relation matrix) i

/-- The geometric realization of a Coxeter system on the free real space on its simple indices. -/
noncomputable def geometricRealization : Realization cs (V := Index →₀ ℝ) where
  simpleRoot := geometricRoot
  root_independent := geometricRoot_linearIndependent
  form := geometricForm matrix
  form_isSymm := geometricForm_isSymm matrix
  form_root := geometricForm_root matrix
  action := geometricAction matrix cs
  action_simple := by
    intro i x
    rw [geometricAction_simple]
    exact geometricReflection_apply matrix i x

/-- The geometric realization has the basis simple roots, cosine form, and geometric action. -/
theorem geometricRealization_spec :
    (geometricRealization matrix cs).simpleRoot = geometricRoot ∧
    (geometricRealization matrix cs).form = geometricForm matrix ∧
    (geometricRealization matrix cs).action = geometricAction matrix cs := ⟨rfl, rfl, rfl⟩

end BruhatIntervals
