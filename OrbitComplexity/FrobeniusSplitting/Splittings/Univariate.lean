import OrbitComplexity.FrobeniusSplitting.Splittings.Polynomial
import OrbitComplexity.FrobeniusSplitting.Splittings.Transport
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Frobenius splittings of univariate polynomial rings

The splitting of a multivariate polynomial ring specializes to a single variable
through the algebra equivalence with the univariate polynomial ring.

## Main definitions

* `FrobeniusSplitting.RingSplitting.univariate`: the univariate splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.univariate_coeff`: extraction of coefficients.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- The multivariate splitting in one variable defines a univariate polynomial splitting. -/
noncomputable def univariate (base : RingSplitting R p) :
    RingSplitting (Polynomial R) p :=
  (base.polynomial (σ := Unit) (expChar_pos R p)).transport
    (MvPolynomial.uniqueAlgEquiv R Unit).toRingEquiv

/-- The univariate splitting extracts coefficients at degrees divisible by the characteristic. -/
theorem univariate_coeff (base : RingSplitting R p) (f : Polynomial R) (n : ℕ) :
    (base.univariate f).coeff n = base (f.coeff (p * n)) := by
  change ((MvPolynomial.uniqueAlgEquiv R Unit)
    ((base.polynomial (expChar_pos R p))
      ((MvPolynomial.uniqueAlgEquiv R Unit).symm f))).coeff n = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, polynomial_coeff,
    MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]

end FrobeniusSplitting.RingSplitting
