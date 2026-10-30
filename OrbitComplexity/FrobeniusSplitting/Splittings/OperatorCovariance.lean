import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring
import Batteries.Tactic.Lint

/-! # Affine covariance of polynomial coefficient operators

The coefficient operator transforms under an affine coordinate change with the
inverse Jacobian power. The calculation uses Frobenius linearity and the
coefficients of polynomials of degree at most `p - 1`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace FrobeniusSplitting

section Rings

variable {R : Type*} [CommRing R] {p : ℕ}

private theorem small_trace (ψ : FrobeniusLinearMap R p)
    (T : FrobeniusLinearMap (Polynomial R) p)
    (hc : ∀ f n, (T f).coeff n = ψ (f.coeff (p * n + (p - 1))))
    (hp : 0 < p) (f : Polynomial R) (hf : f.natDegree ≤ p - 1) :
    T f = C (ψ (f.coeff (p - 1))) := by
  ext n
  rw [hc]
  cases n with
  | zero => simp
  | succ n =>
      have hpos : 0 < p * (n + 1) := Nat.mul_pos hp (Nat.succ_pos n)
      have hdegree : f.natDegree < p * (n + 1) + (p - 1) := by omega
      rw [coeff_eq_zero_of_natDegree_lt hdegree, ψ.map_zero]
      simp

private theorem affine_power_degree (a b c w : R) (n : ℕ) :
    (C w * (C c * (C a * X + C b) ^ n)).natDegree ≤ n := by
  have hpow : ((C a * X + C b) ^ n).natDegree ≤ n := by
    simpa only [Nat.mul_one] using
      (natDegree_pow_le_of_le n (natDegree_linear_le (a := a) (b := b)))
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_C_mul_le _ _).trans hpow)

private theorem affine_power_coeff (a b : R) (n : ℕ) :
    ((C a * X + C b) ^ n).coeff n = a ^ n := by
  simpa using (coeff_pow_of_natDegree_le
    (p := C a * X + C b) (m := n) (natDegree_linear_le (a := a) (b := b)))

private theorem small_affine_trace (ψ : FrobeniusLinearMap R p)
    (T : FrobeniusLinearMap (Polynomial R) p)
    (hc : ∀ f n, (T f).coeff n = ψ (f.coeff (p * n + (p - 1))))
    (hp : 0 < p) (a : Rˣ) (b c : R) (n : ℕ) (hn : n < p) :
    T (C ((↑(a⁻¹) : R) ^ (p - 1)) *
      (C c * (C (a : R) * X + C b) ^ n)) =
      (T (C c * X ^ n)).comp (C (a : R) * X + C b) := by
  have hle : n ≤ p - 1 := by omega
  have hleft := affine_power_degree (a : R) b c ((↑(a⁻¹) : R) ^ (p - 1)) n
  have hright := natDegree_C_mul_X_pow_le c n
  rw [small_trace ψ T hc hp _ (hleft.trans hle),
    small_trace ψ T hc hp _ (hright.trans hle), C_comp]
  congr 2
  by_cases h : n = p - 1
  · subst n
    simp only [coeff_C_mul, coeff_X_pow_self, mul_one]
    rw [affine_power_coeff]
    have hunit : (↑(a⁻¹) : R) ^ (p - 1) * (a : R) ^ (p - 1) = 1 := by
      rw [← mul_pow]
      simp
    calc
      (↑(a⁻¹) : R) ^ (p - 1) * (c * (a : R) ^ (p - 1)) =
          c * ((↑(a⁻¹) : R) ^ (p - 1) * (a : R) ^ (p - 1)) := by ring
      _ = c := by rw [hunit, mul_one]
  · have hlt : n < p - 1 := lt_of_le_of_ne hle h
    rw [coeff_eq_zero_of_natDegree_lt (hleft.trans_lt hlt),
      coeff_eq_zero_of_natDegree_lt (hright.trans_lt hlt)]

private theorem monomial_decomposition (n p : ℕ) (c : R) :
    monomial n c = (X ^ (n / p)) ^ p * (C c * X ^ (n % p)) := by
  rw [← C_mul_X_pow_eq_monomial]
  have hn : n = (n / p) * p + n % p := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n p).symm
  conv_lhs => rw [hn]
  rw [pow_add, pow_mul]
  ring

private theorem affine_trace (ψ : FrobeniusLinearMap R p)
    (T : FrobeniusLinearMap (Polynomial R) p)
    (hc : ∀ f n, (T f).coeff n = ψ (f.coeff (p * n + (p - 1))))
    (hp : 0 < p) (a : Rˣ) (b : R) (f : Polynomial R) :
    T (C ((↑(a⁻¹) : R) ^ (p - 1)) * f.comp (C (a : R) * X + C b)) =
      (T f).comp (C (a : R) * X + C b) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [add_comp, mul_add, T.map_add, hf, hg]
  | monomial n c =>
      let L : Polynomial R := C (a : R) * X + C b
      let w : R := (↑(a⁻¹) : R) ^ (p - 1)
      change T (C w * (monomial n c).comp L) = (T (monomial n c)).comp L
      have hcomp : C w * (monomial n c).comp L =
          (L ^ (n / p)) ^ p * (C w * (C c * L ^ (n % p))) := by
        rw [monomial_decomposition n p c, mul_comp, pow_comp, pow_comp,
          X_comp, mul_comp, C_comp, pow_comp, X_comp]
        ring
      calc
        T (C w * (monomial n c).comp L) =
            T ((L ^ (n / p)) ^ p * (C w * (C c * L ^ (n % p)))) :=
          congrArg T hcomp
        _ = L ^ (n / p) * T (C w * (C c * L ^ (n % p))) := T.map_pow_mul _ _
        _ = L ^ (n / p) * (T (C c * X ^ (n % p))).comp L :=
          congrArg (fun q => L ^ (n / p) * q)
            (small_affine_trace ψ T hc hp a b c (n % p) (Nat.mod_lt n hp))
        _ = (T ((X ^ (n / p)) ^ p * (C c * X ^ (n % p)))).comp L := by
          rw [T.map_pow_mul, mul_comp, pow_comp, X_comp]
        _ = (T (monomial n c)).comp L :=
          congrArg (fun q => (T q).comp L) (monomial_decomposition n p c).symm

end Rings

/-- The polynomial coefficient operator transforms under an affine coordinate
change with the inverse Jacobian to the power `p - 1`. -/
theorem polynomialTraceOfOperator_affine
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (ψ : FrobeniusLinearMap A p) (hp : 0 < p) (a : Aˣ) (b : A)
    (f : Polynomial A) :
    polynomialTraceOfOperator (K := K) ψ
        (C ((↑(a⁻¹) : A) ^ (p - 1)) * f.comp (C (a : A) * X + C b)) =
      (polynomialTraceOfOperator (K := K) ψ f).comp (C (a : A) * X + C b) :=
  affine_trace ψ (polynomialTraceOfOperator (K := K) ψ)
    (polynomialTraceOfOperator_coeff (K := K) ψ) hp a b f


end FrobeniusSplitting
