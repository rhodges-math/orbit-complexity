import OrbitComplexity.FrobeniusSplitting.Splittings.Univariate
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Evaluation at the origin and polynomial splittings -/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- Evaluation at the origin commutes with the polynomial splitting. -/
theorem univariate_eval_zero (base : RingSplitting R p) (f : Polynomial R) :
    (base.univariate f).eval 0 = base (f.eval 0) := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, mul_zero] using
    base.univariate_coeff f 0

end FrobeniusSplitting.RingSplitting
