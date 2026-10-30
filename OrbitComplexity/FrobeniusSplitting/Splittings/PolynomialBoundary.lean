import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import Batteries.Tactic.Lint

/-! # Restriction of a weighted polynomial trace to the zero section -/

set_option autoImplicit false

namespace FrobeniusSplitting

variable {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
variable [CommRing A] [Algebra K A]

/-- A factor of X to the power p-1 makes the weighted trace restrict to the
prior operator weighted by the constant coefficient of the remaining factor. -/
theorem polynomialTrace_weight_eval_zero (ψ : FrobeniusLinearMap A p)
    (P f : Polynomial A) :
    (((polynomialTraceOfOperator (K := K) ψ).weight (P * Polynomial.X ^ (p - 1))) f).eval 0 =
      (ψ.weight (P.eval 0)) (f.eval 0) := by
  rw [FrobeniusLinearMap.weight_apply, FrobeniusLinearMap.weight_apply]
  simp only [← Polynomial.coeff_zero_eq_eval_zero, polynomialTraceOfOperator_coeff,
    Nat.mul_zero, zero_add]
  have h : P * Polynomial.X ^ (p - 1) * f = (P * f) * Polynomial.X ^ (p - 1) := by
    ring
  rw [h, Polynomial.coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self,
    Polynomial.mul_coeff_zero]

end FrobeniusSplitting
