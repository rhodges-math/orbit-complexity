import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryForms
import Mathlib.Algebra.MvPolynomial.Coeff

/-! # Upper triangular substitutions on binary forms -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open MvPolynomial
open scoped Matrix

universe u
variable (R : Type u) [CommRing R]

private theorem upper_monomial (n : ℕ) (a b d : R) (j : Fin (n + 1)) :
    substitution R !![a, b; 0, d] (monomial (exponent n j) 1) =
      ∑ k ∈ Finset.range ((j : ℕ) + 1),
        monomial (Finsupp.single (0 : Fin 2) (n - j) +
          (Finsupp.single (1 : Fin 2) k + Finsupp.single (0 : Fin 2) (j - k)))
          (((j : ℕ).choose k : R) * a ^ (n - j) * b ^ (j - k) * d ^ k) := by
  rw [monomial_fin_two]
  simp [exponent, substitution, Fin.sum_univ_two]
  rw [add_comm (C b * X (0 : Fin 2)), add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [monomial_fin_two]
  simp [map_mul, map_pow, pow_add, mul_pow]
  ring

private theorem exponent_eq (n : ℕ) (i j : Fin (n + 1)) {k : ℕ} (hk : k ≤ j) :
    Finsupp.single (0 : Fin 2) (n - j) +
        (Finsupp.single (1 : Fin 2) k + Finsupp.single (0 : Fin 2) (j - k)) =
      exponent n i ↔ k = i := by
  constructor
  · intro h
    simpa [exponent] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  · rintro rfl
    ext r
    fin_cases r
    · simp [exponent]
      have hj := j.isLt
      omega
    · simp [exponent]

/-- Upper triangular binary-form matrices have the binomial substitution coefficients. -/
theorem matrix_upper (n : ℕ) (a b d : R) (i j : Fin (n + 1)) :
    matrix R n !![a, b; 0, d] i j =
      if (i : ℕ) ≤ j then
        ((j : ℕ).choose i : R) * a ^ (n - j) * b ^ ((j : ℕ) - (i : ℕ)) * d ^ (i : ℕ)
      else 0 := by
  classical
  rw [matrix_apply, upper_monomial]
  simp only [coeff_sum, coeff_monomial]
  have hsum :
      (∑ k ∈ Finset.range ((j : ℕ) + 1),
        if Finsupp.single (0 : Fin 2) (n - j) +
            (Finsupp.single (1 : Fin 2) k + Finsupp.single (0 : Fin 2) (j - k)) =
              exponent n i then
          ((j : ℕ).choose k : R) * a ^ (n - j) * b ^ (j - k) * d ^ k else 0) =
        ∑ k ∈ Finset.range ((j : ℕ) + 1),
          if k = (i : ℕ) then
            ((j : ℕ).choose k : R) * a ^ (n - j) * b ^ (j - k) * d ^ k else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [exponent_eq n i j (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  rw [hsum, Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

end ReductiveGroups.BinaryForms
