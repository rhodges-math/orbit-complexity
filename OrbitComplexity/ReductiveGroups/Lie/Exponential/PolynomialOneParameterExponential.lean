import OrbitComplexity.ReductiveGroups.Lie.Roots.PolynomialOneParameterRecurrence
import OrbitComplexity.ReductiveGroups.Lie.Exponential.PolynomialExponentialUniqueness

/-!
# Polynomial One Parameter Exponential

Polynomial matrix one-parameter groups are finite exponentials. -/

noncomputable section
namespace ReductiveGroups
open Polynomial

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]

/-- The value at `t : K` of a polynomial `p` with matrix coefficients, the matrix `∑ k, t ^ k •
p.coeff k`. -/
def polynomialMatrixValue (p : Polynomial (Matrix ι ι K)) (t : K) : Matrix ι ι K :=
  p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) t)

omit [CharZero K] in
private theorem polynomialMatrix_coeff_zero (p : Polynomial (Matrix ι ι K))
    (hzero : polynomialMatrixValue p 0 = 1) : p.coeff 0 = 1 := by
  simpa [polynomialMatrixValue, Polynomial.eval₂_at_zero] using hzero

/-- The coefficient of the parameter is nilpotent for a polynomial
matrix curve satisfying the additive group law. -/
theorem PolynomialOneParameterExponential.one_parameter_linear_nilpotent
    (p : Polynomial (Matrix ι ι K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ t s : K, polynomialMatrixValue p (t + s) =
      polynomialMatrixValue p t * polynomialMatrixValue p s) :
    IsNilpotent (p.coeff 1) := by
  exact polynomial_exponential_linear_nilpotent p
    (polynomialMatrix_coeff_zero p hzero)
    (PolynomialOneParameterRecurrence.one_parameter_coeff_recurrence p hadd)

/-- A polynomial matrix one-parameter group is the finite
associative exponential of its linear coefficient. -/
theorem polynomial_one_parameter_eq_exponential
    (p : Polynomial (Matrix ι ι K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ t s : K, polynomialMatrixValue p (t + s) =
      polynomialMatrixValue p t * polynomialMatrixValue p s)
    (t : K) :
    polynomialMatrixValue p t =
      associativeExponential (K := K) (t • p.coeff 1) := by
  exact polynomial_exponential_eval p
    (polynomialMatrix_coeff_zero p hzero)
    (PolynomialOneParameterRecurrence.one_parameter_coeff_recurrence p hadd) t

/-- Two polynomial matrix one-parameter groups with the same linear
coefficient agree at every parameter. -/
theorem polynomial_one_parameter_unique
    (p q : Polynomial (Matrix ι ι K))
    (hpzero : polynomialMatrixValue p 0 = 1)
    (hpadd : ∀ t s : K, polynomialMatrixValue p (t + s) =
      polynomialMatrixValue p t * polynomialMatrixValue p s)
    (hqzero : polynomialMatrixValue q 0 = 1)
    (hqadd : ∀ t s : K, polynomialMatrixValue q (t + s) =
      polynomialMatrixValue q t * polynomialMatrixValue q s)
    (hlinear : p.coeff 1 = q.coeff 1) (t : K) :
    polynomialMatrixValue p t = polynomialMatrixValue q t := by
  rw [polynomial_one_parameter_eq_exponential p hpzero hpadd t,
    polynomial_one_parameter_eq_exponential q hqzero hqadd t, hlinear]

/-- A unit-valued additive one-parameter group with polynomial entries
is determined exactly by its polynomial's linear coefficient. -/
theorem PolynomialOneParameterExponential.unit_one_parameter_eq_exponential
    (u : Multiplicative K →* (Matrix ι ι K)ˣ)
    (p : Polynomial (Matrix ι ι K))
    (hu : ∀ t : K, polynomialMatrixValue p t =
      (u (Multiplicative.ofAdd t) : Matrix ι ι K))
    (t : K) :
    (u (Multiplicative.ofAdd t) : Matrix ι ι K) =
      associativeExponential (K := K) (t • p.coeff 1) := by
  have hzero : polynomialMatrixValue p 0 = 1 := by
    simpa using hu 0
  have hadd (a b : K) : polynomialMatrixValue p (a + b) =
      polynomialMatrixValue p a * polynomialMatrixValue p b := by
    rw [hu, hu, hu]
    simp
  rw [← hu]
  exact polynomial_one_parameter_eq_exponential p hzero hadd t

end ReductiveGroups
