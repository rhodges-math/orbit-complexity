import OrbitComplexity.FrobeniusSplitting.Splittings.RegularWeights
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Eval.Degree
import Batteries.Tactic.Lint

/-!
# Polynomial coframe units and top coefficients

A unit comparing two coframes on an affine line over a reduced ring is constant.
A regular top coefficient identifies it after an affine coordinate change.
-/

noncomputable section

universe u

open Polynomial

namespace FrobeniusSplitting

private theorem polynomial_unit_constant {R : Type u} [CommRing R] [IsReduced R]
    (u : (Polynomial R)ˣ) :
    (u : Polynomial R) = C ((u : Polynomial R).coeff 0) := by
  apply Polynomial.ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp
  · rw [coeff_C, ite_eq_right hi]
    exact isNilpotent_iff_eq_zero.mp
      ((Polynomial.coeff_isUnit_isNilpotent_of_isUnit u.isUnit).2 i hi)

private theorem affine_top_coefficient {R : Type u} [CommRing R]
    (Q : Polynomial R) (n : ℕ) (hQ : Q.natDegree ≤ n) (a : Rˣ) (b : R) :
    (Q.comp (C (a : R) * X + C b)).coeff n = Q.coeff n * (a : R) ^ n := by
  nontriviality R
  have ha : (a : R) ≠ 0 := Units.ne_zero a
  have hd : (C (a : R) * X + C b).natDegree = 1 :=
    Polynomial.natDegree_linear ha
  have hl : (C (a : R) * X + C b).leadingCoeff = (a : R) :=
    Polynomial.leadingCoeff_linear ha
  by_cases he : Q.natDegree = n
  · have h := Polynomial.coeff_comp_degree_mul_degree
      (p := Q) (q := C (a : R) * X + C b) (by rw [hd]; decide)
    simpa only [hd, mul_one, hl, ← Polynomial.coeff_natDegree, he] using h
  · have hlt : Q.natDegree < n := lt_of_le_of_ne hQ he
    have hc : (Q.comp (C (a : R) * X + C b)).natDegree ≤ Q.natDegree := by
      calc
        (Q.comp (C (a : R) * X + C b)).natDegree ≤
            Q.natDegree * (C (a : R) * X + C b).natDegree :=
          Polynomial.natDegree_comp_le
        _ = Q.natDegree := by rw [hd, mul_one]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

/-- The top coefficient identifies a polynomial coframe unit after an affine change. -/
theorem polynomialFrameUnit_of_coeff {R : Type u} [CommRing R] [IsReduced R]
    (P Q : Polynomial R) (n : ℕ) (hQ : Q.natDegree ≤ n)
    (a delta : Rˣ) (b : R) (u : (Polynomial R)ˣ)
    (hsection : P = (u : Polynomial R) * Q.comp (C (a : R) * X + C b))
    (hcoeff : P.coeff n = (delta : R) * Q.coeff n)
    (hregular : IsRegular (Q.coeff n)) :
    (u : Polynomial R) = C ((delta : R) * (↑(a⁻¹) : R) ^ n) := by
  have hu := polynomial_unit_constant u
  have he : ((u : Polynomial R).coeff 0 * (a : R) ^ n) * Q.coeff n =
      (delta : R) * Q.coeff n := by
    have h := hcoeff
    rw [hsection, hu, coeff_C_mul, affine_top_coefficient Q n hQ a b] at h
    calc
      ((u : Polynomial R).coeff 0 * (a : R) ^ n) * Q.coeff n =
          (u : Polynomial R).coeff 0 * (Q.coeff n * (a : R) ^ n) := by ac_rfl
      _ = (delta : R) * Q.coeff n := h
  have hf : (u : Polynomial R).coeff 0 * (a : R) ^ n = (delta : R) :=
    hregular.right he
  have hi : (a : R) ^ n * (↑(a⁻¹) : R) ^ n = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  have hc : (u : Polynomial R).coeff 0 = (delta : R) * (↑(a⁻¹) : R) ^ n := by
    calc
      (u : Polynomial R).coeff 0 =
          ((u : Polynomial R).coeff 0 * (a : R) ^ n) * (↑(a⁻¹) : R) ^ n := by
            rw [mul_assoc, hi, mul_one]
      _ = (delta : R) * (↑(a⁻¹) : R) ^ n := by rw [hf]
  exact hu.trans (congrArg C hc)

/-- A normalized prior operator supplies regularity for the coframe-unit calculation. -/
theorem polynomialFrameUnit_of_normalized {R : Type u} [CommRing R] [IsReduced R]
    {p : ℕ} (phi : FrobeniusLinearMap R p) (hp : 0 < p)
    (P Q : Polynomial R) (n : ℕ) (hQ : Q.natDegree ≤ n)
    (a delta : Rˣ) (b : R) (u : (Polynomial R)ˣ)
    (hsection : P = (u : Polynomial R) * Q.comp (C (a : R) * X + C b))
    (hcoeff : P.coeff n = (delta : R) * Q.coeff n)
    (hnormalized : phi (Q.coeff n) = 1) :
    (u : Polynomial R) = C ((delta : R) * (↑(a⁻¹) : R) ^ n) :=
  polynomialFrameUnit_of_coeff P Q n hQ a delta b u hsection hcoeff
    (phi.isRegular_of_normalized hp (Q.coeff n) hnormalized)

end FrobeniusSplitting
