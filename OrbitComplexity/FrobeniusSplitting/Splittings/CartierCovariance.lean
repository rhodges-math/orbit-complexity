import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCoordinates
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import Mathlib.Data.Nat.Choose.Sum

/-! # Translation covariance of the standard one-variable splitting

The scalar factors in the binomial expansion multiply the input of the Frobenius-linear
operators, as in Brion--Kumar, Definitions 4.1.1 and 4.1.4.
-/

namespace FrobeniusSplitting
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]

private theorem standard_weight (base : RingSplitting R p) (f : Polynomial R) :
    univariateTrace base (X ^ (p - 1) * f) = base.univariate f := by
  ext n
  rw [univariateTrace_coeff, coeff_X_pow_mul, RingSplitting.univariate_coeff]

/-- Conjugating the standard splitting by translation translates its Cartier-trace weight. -/
private theorem univariate_conj_translate (base : RingSplitting R p) (a : R) (f : Polynomial R) :
    (base.univariate (f.comp (X - C a))).comp (X + C a) =
      univariateTrace base ((X + C a) ^ (p - 1) * f) := by
  rw [← standard_weight, ← univariateTrace_translate]
  congr 1
  simp only [mul_comp, pow_comp, X_comp, comp_assoc, sub_comp, C_comp,
    add_sub_cancel_right, comp_X]

private theorem translated_weight (a : R) (f : Polynomial R) :
    (X + C a) ^ (p - 1) * f =
      ∑ j ∈ Finset.range p,
        (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j)) * (C (a ^ j) * f) := by
  rw [add_comm (X : Polynomial R), add_pow, Finset.sum_mul,
    Nat.sub_add_cancel (expChar_pos R p)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_pow, map_natCast]
  ring

private theorem translated_trace (base : RingSplitting R p) (a : R) (f : Polynomial R) :
    univariateTrace base ((X + C a) ^ (p - 1) * f) =
      ∑ j ∈ Finset.range p,
        ((univariateTrace base).weight
          (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j))) (C (a ^ j) * f) := by
  rw [translated_weight]
  simpa only [FrobeniusLinearMap.weight_apply] using
    map_sum (univariateTrace base).toAddMonoidHom
      (fun j => (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j)) * (C (a ^ j) * f))
      (Finset.range p)

/-- A translation conjugate is a sum of fewer-than-characteristic input-weighted operators. -/
theorem univariate_conj_translate_sum (base : RingSplitting R p) (a : R) (f : Polynomial R) :
    (base.univariate (f.comp (X - C a))).comp (X + C a) =
      ∑ j ∈ Finset.range p,
        ((univariateTrace base).weight
          (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j))) (C (a ^ j) * f) :=
  (univariate_conj_translate base a f).trans (translated_trace base a f)


end
end FrobeniusSplitting

namespace FrobeniusSplitting
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]

/-- Complementary Laurent weights give the same operator in reciprocal coordinates. -/
private theorem weightedTrace_reciprocal (base : RingSplitting R p) (c : R) (m n : ℕ)
    (hmn : m + n = 2 * (p - 1)) (f : LaurentPolynomial R) :
    laurentTrace base
        (LaurentPolynomial.C c * LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert f) =
      LaurentPolynomial.invert
        (laurentTrace base (LaurentPolynomial.C c * LaurentPolynomial.T (n : ℤ) * f)) := by
  have hexp : 2 * ((p : ℤ) - 1) + -(n : ℤ) = (m : ℤ) := by
    have hp := expChar_pos R p
    have hcast := congrArg (fun q : ℕ => (q : ℤ)) hmn
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp,
      Nat.cast_one] at hcast
    omega
  rw [← laurentTrace_invert]
  congr 1
  simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  calc
    _ = LaurentPolynomial.C c *
        (LaurentPolynomial.T (2 * ((p : ℤ) - 1)) * LaurentPolynomial.T (-(n : ℤ))) *
        LaurentPolynomial.invert f := by rw [← LaurentPolynomial.T_add, hexp]
    _ = _ := by ac_rfl

/-- Polynomial weighted trace extends to the Laurent chart with its identical weight. -/
theorem weightedTrace_toLaurent (base : RingSplitting R p) (c : R) (m : ℕ)
    (f : Polynomial R) :
    laurentTrace base (LaurentPolynomial.C c * LaurentPolynomial.T (m : ℤ) * f.toLaurent) =
      (univariateTrace base (C c * X ^ m * f)).toLaurent := by
  rw [← laurentTrace_toLaurent]
  congr 1
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

/-- The binomial coefficient operator has compatible formulas on both projective charts. -/
theorem canonicalTrace_reciprocal (base : RingSplitting R p) (j : Fin p)
    (f : Polynomial R) :
    laurentTrace base
        (LaurentPolynomial.C ((Nat.choose (p - 1) j : ℕ) : R) *
          LaurentPolynomial.T ((p - 1 - j : ℕ) : ℤ) *
          LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert
        (univariateTrace base
          (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 + j) * f)).toLaurent := by
  rw [weightedTrace_reciprocal base _ (p - 1 - j) (p - 1 + j)]
  · rw [weightedTrace_toLaurent]
  · have hj := j.isLt
    omega

end
end FrobeniusSplitting
