import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentPowerLinearCoefficient

/-!
# Nilpotent Power Logarithm

The tangent coefficient of the finite power curve is the usual finite
logarithmic series. These identities are algebraic; nilpotence will be used
only when this series is related to the exponential. -/

noncomputable section
namespace ReductiveGroups

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

omit [CharZero K] in
/-- The equality is

```lean
(descPochhammer K (k + 1)).coeff 1 = (-1 : K) ^ k * (k.factorial : K)
```
-/
theorem descPochhammer_coeff_one_succ (k : ℕ) :
    (descPochhammer K (k + 1)).coeff 1 = (-1 : K) ^ k * (k.factorial : K) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [descPochhammer_succ_right, mul_sub, Polynomial.coeff_sub,
        Polynomial.coeff_mul_X, ← Polynomial.C_eq_natCast,
        Polynomial.coeff_mul_C, ih]
      have hz : (descPochhammer K (k + 1)).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        exact descPochhammer_ne_zero_eval_zero K (by omega : k + 1 ≠ 0)
      rw [hz, zero_sub, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

/-- The scalar coefficient of the k-th nonconstant power is exactly
the logarithmic coefficient, with the correct alternating sign. -/
theorem descPochhammer_coeff_one_div_factorial (k : ℕ) :
    (descPochhammer K (k + 1)).coeff 1 / ((k + 1).factorial : K) =
      (-1 : K) ^ k / (k + 1 : K) := by
  rw [descPochhammer_coeff_one_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

/-- The polynomial tangent used for the inverse exponential is
the finite logarithm sum, without any infinite-series interpretation. -/
theorem NilpotentPowerPolynomial.coeff_one_eq_logarithm (r : ℕ) (N : A) :
    (nilpotentPowerPolynomial (K := K) (r + 1) N).coeff 1 =
      ∑ k ∈ Finset.range r, ((-1 : K) ^ k / (k + 1 : K)) • N ^ (k + 1) := by
  rw [nilpotentPowerPolynomial_coeff, Finset.sum_range_succ']
  simp only [descPochhammer_zero, Polynomial.coeff_one, one_ne_zero, ↓reduceIte,
    zero_div, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [descPochhammer_coeff_one_div_factorial]

end ReductiveGroups
