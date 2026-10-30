import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryForms
import Mathlib.Algebra.MvPolynomial.Coeff

/-! # Exchanging the two binary-form variables -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open MvPolynomial
open scoped Matrix

universe u
variable (R : Type u) [CommRing R]

private theorem exchange_monomial (n : ℕ) (j : Fin (n + 1)) :
    substitution R !![0, 1; 1, 0] (monomial (exponent n j) 1) =
      monomial (exponent n j.rev) 1 := by
  rw [monomial_fin_two, monomial_fin_two]
  have hj : (j : ℕ) ≤ n := by omega
  simp [exponent, substitution, Fin.sum_univ_two, Fin.val_rev,
    Nat.sub_sub_self hj, mul_comm]

/-- Exchanging the two variables reverses the degree-`n` monomial basis. -/
theorem matrix_exchange (n : ℕ) (i j : Fin (n + 1)) :
    matrix R n !![0, 1; 1, 0] i j = if j.rev = i then 1 else 0 := by
  rw [matrix_apply, exchange_monomial, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h
    apply Fin.ext
    simpa [exponent] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  · rintro rfl
    rfl

/-- Conjugating a two-dimensional matrix by exchange reverses both binary-form indices. -/
theorem matrix_exchange_conjugate (n : ℕ) (a : Matrix (Fin 2) (Fin 2) R)
    (i j : Fin (n + 1)) :
    matrix R n (!![0, 1; 1, 0] * a * !![0, 1; 1, 0]) i j =
      matrix R n a i.rev j.rev := by
  classical
  rw [matrix_mul, matrix_mul]
  simp only [Matrix.mul_apply, matrix_exchange, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [ite_mul, one_mul, zero_mul, Fin.rev_eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ReductiveGroups.BinaryForms
