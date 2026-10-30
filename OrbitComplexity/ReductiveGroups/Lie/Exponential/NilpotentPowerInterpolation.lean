import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Nilpotent Power Interpolation

A finite falling-factorial interpolation of natural powers of a
unipotent element in an associative algebra. -/

noncomputable section
namespace ReductiveGroups

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

/-- A finite polynomial expression in `t`, with coefficients in powers
of the nilpotent element `N`. -/
def nilpotentPowerCurve (r : ℕ) (N : A) (t : K) : A :=
  ∑ k ∈ Finset.range r,
    ((descPochhammer K k).eval t / (k.factorial : K)) • N ^ k

/-- A polynomial over the possibly noncommutative coefficient
ring `A` whose evaluation along central scalar parameters is the curve. -/
def nilpotentPowerPolynomial (r : ℕ) (N : A) : Polynomial A :=
  ∑ k ∈ Finset.range r,
    Polynomial.C ((k.factorial : K)⁻¹ • N ^ k) *
      (descPochhammer K k).map (algebraMap K A)

omit [CharZero K] in
/-- The equality is

```lean
(nilpotentPowerPolynomial (K := K) r N).eval (algebraMap K A t) =
      nilpotentPowerCurve (K := K) r N t
```
-/
theorem nilpotentPowerPolynomial_eval (r : ℕ) (N : A) (t : K) :
    (nilpotentPowerPolynomial (K := K) r N).eval (algebraMap K A t) =
      nilpotentPowerCurve (K := K) r N t := by
  unfold nilpotentPowerPolynomial nilpotentPowerCurve
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_C_mul, Polynomial.eval_map,
    Polynomial.eval₂_at_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  simpa only [div_eq_mul_inv, map_mul, mul_assoc] using
    (Algebra.commutes ((descPochhammer K k).eval t)
      (algebraMap K A ((k.factorial : K)⁻¹) * N ^ k)).symm

omit [CharZero K] in
private theorem one_add_pow_binomial (N : A) (m : ℕ) :
    (1 + N) ^ m =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : K) • N ^ k := by
  rw [Commute.add_pow (Commute.one_left N) m]
  rw [← Finset.sum_range_reflect
    (fun k => (1 : A) ^ k * N ^ (m - k) * (m.choose k : A)) (m + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel_right, one_pow, one_mul]
  have hsub : m - (m - k) = k := by omega
  rw [hsub, Nat.choose_symm hkm]
  rw [Algebra.smul_def]
  simpa only [map_natCast, Nat.cast_ofNat] using
    (Nat.cast_comm (m.choose k) (N ^ k)).symm

private theorem sum_binomial_truncate (N : A) (r m : ℕ)
    (hNr : N ^ r = 0) :
    (∑ k ∈ Finset.range r, (m.choose k : K) • N ^ k) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : K) • N ^ k := by
  by_cases h : r ≤ m + 1
  ·
    have htail : (∑ k ∈ Finset.range ((m + 1) - r),
        (m.choose (r + k) : K) • N ^ (r + k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [pow_eq_zero_of_le (Nat.le_add_right r k) hNr, smul_zero]
    calc
      (∑ k ∈ Finset.range r, (m.choose k : K) • N ^ k) =
          (∑ k ∈ Finset.range r, (m.choose k : K) • N ^ k) + 0 := by rw [add_zero]
      _ = (∑ k ∈ Finset.range r, (m.choose k : K) • N ^ k) +
          (∑ k ∈ Finset.range ((m + 1) - r),
            (m.choose (r + k) : K) • N ^ (r + k)) := by rw [htail]
      _ = ∑ k ∈ Finset.range (m + 1), (m.choose k : K) • N ^ k := by
        rw [← Finset.sum_range_add, Nat.add_sub_of_le h]
  · have h' : m + 1 ≤ r := by omega
    have htail : (∑ k ∈ Finset.range (r - (m + 1)),
        (m.choose (m + 1 + k) : K) • N ^ (m + 1 + k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Nat.choose_eq_zero_of_lt (by omega : m < m + 1 + k)]
      simp
    calc
      (∑ k ∈ Finset.range r, (m.choose k : K) • N ^ k) =
          (∑ k ∈ Finset.range (m + 1), (m.choose k : K) • N ^ k) +
          (∑ k ∈ Finset.range (r - (m + 1)),
            (m.choose (m + 1 + k) : K) • N ^ (m + 1 + k)) := by
            rw [← Finset.sum_range_add, Nat.add_sub_of_le h']
      _ = ∑ k ∈ Finset.range (m + 1), (m.choose k : K) • N ^ k := by rw [htail, add_zero]

/-- At every natural parameter the explicit finite polynomial curve is
the natural power of `1+N`. -/
theorem nilpotentPowerCurve_nat (r : ℕ) (N : A) (hNr : N ^ r = 0) (m : ℕ) :
    nilpotentPowerCurve (K := K) r N (m : K) = (1 + N) ^ m := by
  unfold nilpotentPowerCurve
  simp_rw [← Nat.cast_choose_eq_descPochhammer_div K m]
  rw [one_add_pow_binomial (K := K)]
  exact sum_binomial_truncate N r m hNr

/-- The equality is

```lean
nilpotentPowerCurve (K := K) r N 0 = 1
```
-/
theorem nilpotentPowerCurve_zero (r : ℕ) (N : A)
    (hr : 0 < r) : nilpotentPowerCurve (K := K) r N 0 = 1 := by
  unfold nilpotentPowerCurve
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hr)]
  · simp
  · intro k hk hne
    simp [hne]

/-- The equality is

```lean
nilpotentPowerCurve (K := K) r N 1 = 1 + N
```
-/
theorem nilpotentPowerCurve_one (r : ℕ) (N : A)
    (hNr : N ^ r = 0) : nilpotentPowerCurve (K := K) r N 1 = 1 + N := by
  simpa using nilpotentPowerCurve_nat (K := K) r N hNr 1

end ReductiveGroups
