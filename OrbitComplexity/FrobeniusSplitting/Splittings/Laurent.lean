import OrbitComplexity.FrobeniusSplitting.Splittings.GroupAlgebra
import OrbitComplexity.FrobeniusSplitting.Splittings.Univariate
import OrbitComplexity.FrobeniusSplitting.Splittings.Localization
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Frobenius splittings in Laurent coordinates

The group algebra splitting for integer exponents commutes with coordinate
inversion. The univariate splitting extends to the same Laurent splitting by
localization at the variable. These identities identify the formulas in two
reciprocal coordinates.

## Main definitions

* `FrobeniusSplitting.RingSplitting.laurent`: the Laurent polynomial splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.laurent_invert`: compatibility with inversion.
* `FrobeniusSplitting.RingSplitting.laurent_toLaurent`: compatibility with inclusion.
* `FrobeniusSplitting.RingSplitting.laurent_eq_localize`: compatibility with localization.
-/

namespace FrobeniusSplitting.RingSplitting

section Semiring

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

private theorem intScale_injective (hp : 0 < p) :
    Function.Injective (fun n : ℤ ↦ p • n) :=
  fun _ _ h ↦ (nsmul_right_inj hp.ne_zero).1 h

/-- Coefficient splitting and division of integer exponents split Laurent polynomials. -/
noncomputable def laurent (base : RingSplitting R p) :
    RingSplitting (LaurentPolynomial R) p :=
  base.addMonoidAlgebra (intScale_injective (expChar_pos R p))

/-- The Laurent splitting extracts coefficients at exponents divisible by the characteristic. -/
theorem laurent_coeff (base : RingSplitting R p) (f : LaurentPolynomial R) (n : ℤ) :
    (base.laurent f).coeff n = base (f.coeff (p • n)) := rfl

/-- Inverting the Laurent coordinate commutes with its splitting. -/
theorem laurent_invert (base : RingSplitting R p) (f : LaurentPolynomial R) :
    base.laurent (LaurentPolynomial.invert f) = LaurentPolynomial.invert (base.laurent f) := by
  ext n
  rw [laurent_coeff, LaurentPolynomial.invert_apply, LaurentPolynomial.invert_apply,
    laurent_coeff, smul_neg]

private theorem toLaurent_coeff_nat (f : Polynomial R) (n : ℕ) :
    f.toLaurent.coeff (n : ℤ) = f.coeff n := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) (n : ℤ) = f.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

private theorem toLaurent_coeff_neg (f : Polynomial R) (n : ℤ) (hn : n < 0) :
    f.toLaurent.coeff n = 0 := by
  change (Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ)) f.toFinsupp.coeff) n = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  rw [← hm] at hn
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

/-- Including ordinary polynomials in Laurent polynomials commutes with splitting. -/
theorem laurent_toLaurent (base : RingSplitting R p) (f : Polynomial R) :
    base.laurent f.toLaurent = (base.univariate f).toLaurent := by
  ext n
  cases n with
  | ofNat n =>
    rw [laurent_coeff]
    change base (f.toLaurent.coeff (p • (n : ℤ))) =
      (base.univariate f).toLaurent.coeff (n : ℤ)
    have hmul : p • (n : ℤ) = ((p * n : ℕ) : ℤ) := by
      simp only [nsmul_eq_mul, Nat.cast_mul]
    rw [hmul, toLaurent_coeff_nat, toLaurent_coeff_nat, univariate_coeff]
  | negSucc n =>
    have hneg : p • Int.negSucc n < 0 := by
      change (p : ℤ) * Int.negSucc n < 0
      exact mul_neg_of_pos_of_neg (Int.natCast_pos.mpr (expChar_pos R p))
        (Int.negSucc_lt_zero n)
    rw [laurent_coeff, toLaurent_coeff_neg f _ hneg,
      toLaurent_coeff_neg (base.univariate f) _ (Int.negSucc_lt_zero n), base.map_zero]

end Semiring

/-- The Laurent splitting is the localization of the univariate splitting at its variable. -/
theorem laurent_eq_localize {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    (base : RingSplitting R p) :
    base.laurent = base.univariate.localize (Submonoid.powers Polynomial.X)
      (expChar_pos R p) := by
  apply Eq.symm
  apply base.univariate.localize_eq (Submonoid.powers Polynomial.X) (expChar_pos R p)
  intro f
  exact base.laurent_toLaurent f

end FrobeniusSplitting.RingSplitting
