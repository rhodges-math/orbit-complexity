import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial Exponential Uniqueness

A polynomial with the exponential coefficient recurrence is a finite exponential. -/

noncomputable section

namespace ReductiveGroups

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

variable (p : Polynomial A)

/-- The recurrence determines every coefficient from the linear coefficient. -/
theorem polynomial_exponential_coefficients
    (hzero : p.coeff 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : K) • p.coeff (n + 1) =
      p.coeff n * p.coeff 1) (n : ℕ) :
    p.coeff n = ((n.factorial : K)⁻¹) • (p.coeff 1) ^ n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have h := congrArg (fun a : A => ((n + 1 : K)⁻¹) • a) (hrec n)
      simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at h
      rw [ih] at h
      calc
        p.coeff (n + 1) = (n + 1 : K)⁻¹ •
            ((((n.factorial : K)⁻¹) • (p.coeff 1) ^ n) * p.coeff 1) := h
        _ = (((n + 1).factorial : K)⁻¹) • (p.coeff 1) ^ (n + 1) := by
          rw [smul_mul_assoc, smul_smul, pow_succ, Nat.factorial_succ]
          congr 1
          simp [mul_inv_rev, mul_comm]

/-- The coefficient of `X` is nilpotent because the polynomial has bounded degree. -/
theorem polynomial_exponential_linear_nilpotent
    (hzero : p.coeff 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : K) • p.coeff (n + 1) =
      p.coeff n * p.coeff 1) :
    IsNilpotent (p.coeff 1) := by
  let n := p.natDegree + 1
  have hcoeff : p.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [polynomial_exponential_coefficients p hzero hrec n] at hcoeff
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  refine ⟨n, ?_⟩
  have h := congrArg (fun a : A => (n.factorial : K) • a) hcoeff
  simpa [smul_smul, hn] using h

/-- Evaluating the polynomial at a central scalar gives the finite exponential. -/
theorem polynomial_exponential_eval
    (hzero : p.coeff 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : K) • p.coeff (n + 1) =
      p.coeff n * p.coeff 1) (t : K) :
    p.eval₂ (RingHom.id A) (algebraMap K A t) =
      associativeExponential (K := K) (t • p.coeff 1) :=
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  by
    let n := p.natDegree + 1
    have hcoeff : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    rw [polynomial_exponential_coefficients p hzero hrec n] at hcoeff
    have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hxn : (p.coeff 1) ^ n = 0 := by
      have h := congrArg (fun a : A => (n.factorial : K) • a) hcoeff
      simpa [smul_smul, hn] using h
    have htn : (t • p.coeff 1) ^ n = 0 := by
      rw [smul_pow, hxn, smul_zero]
    change p.eval₂ (RingHom.id A) (algebraMap K A t) =
      IsNilpotent.exp (t • p.coeff 1)
    rw [Polynomial.eval₂_eq_sum_range' (RingHom.id A)
      (Nat.lt_succ_self p.natDegree) (algebraMap K A t),
      IsNilpotent.exp_eq_sum htn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [polynomial_exponential_coefficients p hzero hrec i]
    simp only [RingHom.id_apply]
    change ((i.factorial : K)⁻¹) • (p.coeff 1) ^ i *
      (algebraMap K A t) ^ i =
        (algebraMap ℚ K ((i.factorial : ℚ)⁻¹)) • (t • p.coeff 1) ^ i
    simp only [map_inv₀, map_natCast]
    rw [smul_pow, ← map_pow (algebraMap K A), smul_mul_assoc,
      ← Algebra.commutes (t ^ i) ((p.coeff 1) ^ i), ← Algebra.smul_def]

end ReductiveGroups
