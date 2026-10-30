import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentPowerInterpolation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Nilpotent Power Curve Law

Polynomial identity over central scalar parameters with coefficients in
a possibly noncommutative algebra, then the nilpotent power curve law. -/

noncomputable section
namespace ReductiveGroups

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

private def polynomialLinearImage (f : A →ₗ[K] K) (p : Polynomial A) : Polynomial K :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial i (f (p.coeff i))

omit [CharZero K] in
private theorem polynomialLinearImage_coeff (f : A →ₗ[K] K)
    (p : Polynomial A) (n : ℕ) :
    (polynomialLinearImage f p).coeff n = f (p.coeff n) := by
  rw [polynomialLinearImage, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ Finset.range (p.natDegree + 1)
  · simp [hn]
  · have hp : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
      (by have hh : p.natDegree + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
          omega)
    simp [hn, hp]

omit [CharZero K] in
private theorem polynomialLinearImage_eval (f : A →ₗ[K] K)
    (p : Polynomial A) (t : K) :
    (polynomialLinearImage f p).eval t =
      f (p.eval (algebraMap K A t)) := by
  rw [polynomialLinearImage, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_monomial]
  rw [Polynomial.eval_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← map_pow, ← Algebra.commutes (t ^ i) (p.coeff i)]
  rw [← Algebra.smul_def, map_smul]
  simp only [smul_eq_mul, mul_comm]

private theorem polynomial_eq_of_eval_nat_scalar
    (p q : Polynomial A)
    (h : ∀ n : ℕ, p.eval (algebraMap K A (n : K)) =
      q.eval (algebraMap K A (n : K))) : p = q := by
  apply Polynomial.ext
  intro i
  apply Module.eval_apply_injective K
  ext f
  have heq : polynomialLinearImage f p = polynomialLinearImage f q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      (Nat.cast_injective (R := K))).mono
    rintro t ⟨n, rfl⟩
    change (polynomialLinearImage f p).eval (n : K) =
      (polynomialLinearImage f q).eval (n : K)
    rw [polynomialLinearImage_eval, polynomialLinearImage_eval, h n]
  have hc := congrArg (fun w : Polynomial K => w.coeff i) heq
  change f (p.coeff i) = f (q.coeff i)
  simpa only [polynomialLinearImage_coeff] using hc

private def weightedNilpotentPolynomial (r : ℕ) (N : A)
    (w : ℕ → Polynomial K) : Polynomial A :=
  ∑ k ∈ Finset.range r,
    Polynomial.C ((k.factorial : K)⁻¹ • N ^ k) *
      (w k).map (algebraMap K A)

omit [CharZero K] in
private theorem weightedNilpotentPolynomial_eval (r : ℕ) (N : A)
    (w : ℕ → Polynomial K) (t : K) :
    (weightedNilpotentPolynomial r N w).eval (algebraMap K A t) =
      ∑ k ∈ Finset.range r,
        ((w k).eval t / (k.factorial : K)) • N ^ k := by
  unfold weightedNilpotentPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_C_mul, Polynomial.eval_map,
    Polynomial.eval₂_at_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  simpa only [div_eq_mul_inv, map_mul, mul_assoc] using
    (Algebra.commutes ((w k).eval t)
      (algebraMap K A ((k.factorial : K)⁻¹) * N ^ k)).symm

private def shiftedNilpotentPowerPolynomial (r : ℕ) (N : A) (s : K) :
    Polynomial A :=
  weightedNilpotentPolynomial r N
    (fun k => (descPochhammer K k).comp (Polynomial.X + Polynomial.C s))

omit [CharZero K] in
private theorem shiftedNilpotentPowerPolynomial_eval
    (r : ℕ) (N : A) (s t : K) :
    (shiftedNilpotentPowerPolynomial r N s).eval (algebraMap K A t) =
      nilpotentPowerCurve (K := K) r N (s + t) := by
  rw [shiftedNilpotentPowerPolynomial, weightedNilpotentPolynomial_eval]
  unfold nilpotentPowerCurve
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [add_comm t s]

omit [CharZero K] in
private theorem polynomial_eval_mul_C_at_scalar
    (p : Polynomial A) (c : A) (t : K) :
    (p * Polynomial.C c).eval (algebraMap K A t) =
      p.eval (algebraMap K A t) * c := by
  have h := Polynomial.eval₂_mul_noncomm (RingHom.id A)
    (algebraMap K A t) (p := p) (q := Polynomial.C c)
    (fun k => Algebra.commute_algebraMap_right t
      ((Polynomial.C c).coeff k))
  simpa only [Polynomial.eval₂_id, Polynomial.eval₂_C, RingHom.id_apply] using h

private theorem nilpotentPowerCurve_add_nat_right
    (r : ℕ) (N : A) (hNr : N ^ r = 0) (n : ℕ) (t : K) :
    nilpotentPowerCurve (K := K) r N (t + n) =
      nilpotentPowerCurve (K := K) r N t * (1 + N) ^ n := by
  let P := nilpotentPowerPolynomial (K := K) r N
  let S := shiftedNilpotentPowerPolynomial (K := K) r N (n : K)
  let R := P * Polynomial.C ((1 + N) ^ n)
  have hSR : S = R := by
    apply polynomial_eq_of_eval_nat_scalar (K := K)
    intro m
    change (shiftedNilpotentPowerPolynomial (K := K) r N (n : K)).eval
      (algebraMap K A (m : K)) =
      (nilpotentPowerPolynomial (K := K) r N *
        Polynomial.C ((1 + N) ^ n)).eval (algebraMap K A (m : K))
    rw [shiftedNilpotentPowerPolynomial_eval]
    rw [polynomial_eval_mul_C_at_scalar,
      nilpotentPowerPolynomial_eval]
    have hcast : ((n : K) + (m : K)) = ((n + m : ℕ) : K) := by simp
    rw [hcast, nilpotentPowerCurve_nat (K := K) r N hNr (n + m)]
    rw [Nat.add_comm n m, pow_add]
    rw [nilpotentPowerCurve_nat (K := K) r N hNr m]
  have hev := congrArg (fun p : Polynomial A =>
    p.eval (algebraMap K A t)) hSR
  change (shiftedNilpotentPowerPolynomial (K := K) r N (n : K)).eval
    (algebraMap K A t) =
      (nilpotentPowerPolynomial (K := K) r N *
        Polynomial.C ((1 + N) ^ n)).eval (algebraMap K A t) at hev
  rw [shiftedNilpotentPowerPolynomial_eval,
    polynomial_eval_mul_C_at_scalar,
    nilpotentPowerPolynomial_eval] at hev
  simpa only [add_comm (n : K) t] using hev

/-- The finite falling-factorial interpolation is an additive-to-
multiplicative one-parameter law over the scalar field. -/
theorem nilpotentPowerCurve_add
    (r : ℕ) (N : A) (hNr : N ^ r = 0) (s t : K) :
    nilpotentPowerCurve (K := K) r N (s + t) =
      nilpotentPowerCurve (K := K) r N s *
        nilpotentPowerCurve (K := K) r N t := by
  let P := nilpotentPowerPolynomial (K := K) r N
  let S := shiftedNilpotentPowerPolynomial (K := K) r N s
  let R := Polynomial.C (nilpotentPowerCurve (K := K) r N s) * P
  have hSR : S = R := by
    apply polynomial_eq_of_eval_nat_scalar (K := K)
    intro n
    change (shiftedNilpotentPowerPolynomial (K := K) r N s).eval
      (algebraMap K A (n : K)) =
      (Polynomial.C (nilpotentPowerCurve (K := K) r N s) *
        nilpotentPowerPolynomial (K := K) r N).eval (algebraMap K A (n : K))
    rw [shiftedNilpotentPowerPolynomial_eval]
    rw [Polynomial.eval_C_mul,
      nilpotentPowerPolynomial_eval]
    rw [nilpotentPowerCurve_add_nat_right r N hNr n s,
      nilpotentPowerCurve_nat (K := K) r N hNr n]
  have hev := congrArg (fun p : Polynomial A =>
    p.eval (algebraMap K A t)) hSR
  change (shiftedNilpotentPowerPolynomial (K := K) r N s).eval
    (algebraMap K A t) =
      (Polynomial.C (nilpotentPowerCurve (K := K) r N s) *
        nilpotentPowerPolynomial (K := K) r N).eval
        (algebraMap K A t) at hev
  rw [shiftedNilpotentPowerPolynomial_eval,
    Polynomial.eval_C_mul,
    nilpotentPowerPolynomial_eval] at hev
  exact hev

end ReductiveGroups
