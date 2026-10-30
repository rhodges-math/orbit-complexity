import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import Batteries.Tactic.Lint

/-! # Constant values of polynomial trace operators -/

set_option autoImplicit false

noncomputable section

namespace FrobeniusSplitting

variable {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
  [CommRing A] [Algebra K A]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialNormalization: polynomialTraceOfOperator_constant"
    (← IO.getStderr).flush

/-- Below the second trace exponent, polynomial trace is the constant given by
the coefficient in degree `p - 1`. -/
theorem polynomialTraceOfOperator_constant (ψ : FrobeniusLinearMap A p)
    (f : Polynomial A) (hf : f.natDegree < p + (p - 1)) :
    polynomialTraceOfOperator (K := K) ψ f = Polynomial.C (ψ (f.coeff (p - 1))) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [polynomialTraceOfOperator_coeff, Nat.mul_zero, zero_add,
      Polynomial.coeff_C_zero]
  · have hmul : p ≤ p * n := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left p (Nat.one_le_iff_ne_zero.mpr hn)
    have hdeg : f.natDegree < p * n + (p - 1) :=
      lt_of_lt_of_le hf (Nat.add_le_add_right hmul (p - 1))
    rw [polynomialTraceOfOperator_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, map_zero]
    simp [Polynomial.coeff_C, hn]

end FrobeniusSplitting
