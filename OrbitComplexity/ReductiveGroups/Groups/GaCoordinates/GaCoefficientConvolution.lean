import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentCoordinate
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Basis

/-!
# Ga Coefficient Convolution

Convolution of the additive group's coefficient functionals. -/

noncomputable section
namespace ReductiveGroups
open WithConv
open scoped TensorProduct

variable (K : Type*) [Field K]

/-- The `K`-linear functional on the additive group's coordinate algebra `SymmetricAlgebra K K`
taking the `n`-th coefficient in polynomial coordinates. -/
def gaCoefficientLinear (n : ℕ) : SymmetricAlgebra K K →ₗ[K] K :=
  (Polynomial.lcoeff K n).comp (gaPolynomialEquiv K).toLinearMap

/-- The equality is

```lean
gaCoefficientLinear K n a = (gaPolynomialEquiv K a).coeff n
```
-/
@[simp] theorem gaCoefficientLinear_apply (n : ℕ) (a : SymmetricAlgebra K K) :
    gaCoefficientLinear K n a = (gaPolynomialEquiv K a).coeff n := rfl

private theorem gaCoefficientLinear_conv_generator_pow (n m : ℕ) :
    (toConv (gaCoefficientLinear K n) * toConv (gaCoefficientLinear K 1)).ofConv
      ((SymmetricAlgebra.ι K K 1) ^ m) =
      (n + 1 : K) * gaCoefficientLinear K (n + 1)
        ((SymmetricAlgebra.ι K K 1) ^ m) := by
  rw [LinearMap.convMul_apply, Bialgebra.comul_pow, SymmetricAlgebra.comul_ι, add_pow]
  simp only [map_sum]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  simp only [← nsmul_eq_mul', map_nsmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
  simp [gaCoefficientLinear_apply, Polynomial.coeff_X_pow]
  by_cases h : n + 1 = m
  · subst m
    rw [Finset.sum_eq_single n]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hn
      exact False.elim (hn (by simp))
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : n = j
    · subst j
      have hm : 1 ≠ m - n := by omega
      simp [hm]
    · simp [hj]

/-- Convolution with the linear coefficient raises the coefficient index,
with the exact positive integer factor. -/
theorem gaCoefficientLinear_conv_one (n : ℕ) :
    toConv (gaCoefficientLinear K n) * toConv (gaCoefficientLinear K 1) =
      (n + 1 : K) • toConv (gaCoefficientLinear K (n + 1)) := by
  ext a
  obtain ⟨p, rfl⟩ := (gaPolynomialEquiv K).symm.surjective a
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, LinearMap.add_apply, mul_add] using congrArg₂ HAdd.hAdd hp hq
  | monomial m r =>
      have hpre : (gaPolynomialEquiv K).symm (Polynomial.monomial m r) =
          r • (SymmetricAlgebra.ι K K 1) ^ m := by
        apply (gaPolynomialEquiv K).injective
        simp only [AlgEquiv.apply_symm_apply, map_smul, map_pow,
          gaPolynomialEquiv_generator]
        rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hpre]
      change ((toConv (gaCoefficientLinear K n) *
        toConv (gaCoefficientLinear K 1)).ofConv) (r • _) = _
      rw [map_smul]
      change r * _ = (n + 1 : K) * gaCoefficientLinear K (n + 1) (r • _)
      rw [map_smul, gaCoefficientLinear_conv_generator_pow]
      simp only [smul_eq_mul]
      ring

/-- The equality is

```lean
toConv (gaCoefficientLinear K 0) =
      (1 : WithConv (SymmetricAlgebra K K →ₗ[K] K))
```
-/
@[simp] theorem gaCoefficientLinear_zero :
    toConv (gaCoefficientLinear K 0) =
      (1 : WithConv (SymmetricAlgebra K K →ₗ[K] K)) := by
  ext a
  exact gaPolynomialEquiv_coeff_zero K a

/-- The `n`th convolution power of the linear coefficient is `n!` times
the `n`th coefficient functional of the additive group. -/
theorem gaCoefficientLinear_factorial (n : ℕ) :
    toConv (gaCoefficientLinear K 1) ^ n =
      (n.factorial : K) • toConv (gaCoefficientLinear K n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, smul_mul_assoc, gaCoefficientLinear_conv_one, smul_smul]
      rw [Nat.factorial_succ, Nat.cast_mul]
      congr 1
      simp [mul_comm]

/-- Origin-tangent convolution powers extract every polynomial
coefficient with its factorial,. -/
theorem gaOriginDerivation_pow_coeff (n : ℕ) (a : SymmetricAlgebra K K) :
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (SymmetricAlgebra K K) K
      (((toConv (gaOriginDerivation K : SymmetricAlgebra K K →ₗ[K]
        TauCeti.Bialgebra.CounitAlgebra K (SymmetricAlgebra K K) K)) ^ n).ofConv a) =
      (n.factorial : K) * (gaPolynomialEquiv K a).coeff n := by
  change ((toConv (gaCoefficientLinear K 1)) ^ n).ofConv a = _
  rw [gaCoefficientLinear_factorial]
  rfl

end ReductiveGroups
