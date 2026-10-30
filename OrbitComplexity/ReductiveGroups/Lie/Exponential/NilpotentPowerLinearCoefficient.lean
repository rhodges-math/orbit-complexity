import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentPowerInterpolation

/-!
# Nilpotent Power Linear Coefficient

The tangent of the binomial power polynomial is itself an explicit
finite polynomial in the original algebra element.  -/

noncomputable section
namespace ReductiveGroups

variable {K A C : Type*} [Field K] [Ring A] [Algebra K A]
  [Ring C] [Algebra K C]

/-- The linear coefficient of the power interpolation is a finite
polynomial in `N`, with scalar coefficients from falling factorials. -/
theorem nilpotentPowerPolynomial_coeff (r : ℕ) (N : A) (j : ℕ) :
    (nilpotentPowerPolynomial (K := K) r N).coeff j =
      ∑ k ∈ Finset.range r,
        ((descPochhammer K k).coeff j / (k.factorial : K)) • N ^ k := by
  rw [nilpotentPowerPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  rw [Algebra.smul_def, Algebra.smul_def]
  rw [div_eq_mul_inv, map_mul]
  have hc := Algebra.commutes ((descPochhammer K k).coeff j) (N ^ k)
  calc
    (algebraMap K A ((k.factorial : K)⁻¹) * N ^ k) *
        algebraMap K A ((descPochhammer K k).coeff j) =
        algebraMap K A ((k.factorial : K)⁻¹) *
          (algebraMap K A ((descPochhammer K k).coeff j) * N ^ k) := by
            rw [mul_assoc, ← hc]
    _ = (algebraMap K A ((descPochhammer K k).coeff j) *
        algebraMap K A ((k.factorial : K)⁻¹)) * N ^ k := by
          rw [← mul_assoc, ← map_mul, mul_comm, map_mul]

/-- Applying an algebra homomorphism commutes with every coefficient
of the finite power polynomial, including its tangent coefficient. -/
theorem nilpotentPowerPolynomial_coeff_map (r : ℕ) (N : A)
    (f : A →ₐ[K] C) (j : ℕ) :
    f ((nilpotentPowerPolynomial (K := K) r N).coeff j) =
      (nilpotentPowerPolynomial (K := K) r (f N)).coeff j := by
  simp only [nilpotentPowerPolynomial_coeff, map_sum, map_smul, map_pow]

end ReductiveGroups
