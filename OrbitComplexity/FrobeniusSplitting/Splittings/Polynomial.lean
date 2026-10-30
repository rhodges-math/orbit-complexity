import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Polynomial Frobenius splittings

A splitting of the coefficient ring extends to a polynomial ring by keeping the
monomials whose exponents are divisible by the characteristic and applying the
coefficient splitting. The construction is expressed by its coefficient at every
monomial, so it applies to any set of variables.

## References

* Brion and Kumar, *Frobenius splitting methods in geometry and representation
  theory*, Section 1.1.
-/

namespace FrobeniusSplitting.RingSplitting

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p : ℕ}

private theorem exponent_injective (hp : 0 < p) :
    Function.Injective (fun d : σ →₀ ℕ ↦ p • d) :=
  fun _ _ h ↦ (nsmul_right_inj hp.ne_zero).1 h

private noncomputable def polynomialMap (base : RingSplitting R p) (hp : 0 < p) :
    MvPolynomial σ R →+ MvPolynomial σ R where
  toFun f := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange base base.map_zero
    (Finsupp.comapDomain (fun d : σ →₀ ℕ ↦ p • d) (AddMonoidAlgebra.coeff f)
      (exponent_injective hp).injOn))
  map_zero' := by
    ext d
    exact base.map_zero
  map_add' f g := by
    ext d
    exact base.map_add (f.coeff (p • d)) (g.coeff (p • d))

private theorem polynomialMap_coeff (base : RingSplitting R p) (hp : 0 < p)
    (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (polynomialMap base hp f).coeff d = base (f.coeff (p • d)) := rfl

private theorem polynomialMap_monomial (base : RingSplitting R p) (hp : 0 < p)
    (a : σ →₀ ℕ) (r : R) (g : MvPolynomial σ R) :
    polynomialMap base hp ((monomial a r) ^ p * g) =
      monomial a r * polynomialMap base hp g := by
  classical
  ext d
  have hle : p • a ≤ p • d ↔ a ≤ d := by
    simp only [Finsupp.le_def, Finsupp.smul_apply, smul_eq_mul, mul_le_mul_iff_right₀ hp]
  have hsub : p • d - p • a = p • (d - a) := by
    ext i
    simp only [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_sub_left_distrib]
  rw [polynomialMap_coeff, monomial_pow, coeff_monomial_mul', coeff_monomial_mul']
  by_cases h : a ≤ d
  · rw [ite_eq_left (hle.2 h), ite_eq_left h, hsub, base.map_pow_mul, polynomialMap_coeff]
  · rw [ite_eq_right (hle.not.2 h), ite_eq_right h, base.map_zero]

/-- The coefficient splitting and division of exponents extend a splitting to polynomials. -/
noncomputable def polynomial [ExpChar R p] (base : RingSplitting R p) (hp : 0 < p) :
    RingSplitting (MvPolynomial σ R) p where
  toAddMonoidHom := polynomialMap base hp
  map_pow_mul' a b := by
    change polynomialMap base hp (a ^ p * b) = a * polynomialMap base hp b
    refine MvPolynomial.induction_on' a (fun d r ↦ polynomialMap_monomial base hp d r b) ?_
    intro f g hf hg
    rw [add_pow_expChar, add_mul, (polynomialMap base hp).map_add, hf, hg, add_mul]
  map_one' := by
    classical
    ext d
    rw [polynomialMap_coeff]
    by_cases hd : d = 0
    · subst d
      simp only [smul_zero, coeff_one, ite_true]
      exact base.map_one
    · have hpd : 0 ≠ p • d := by
        intro hzero
        apply hd
        apply exponent_injective hp
        simpa only [smul_zero] using hzero.symm
      simp only [coeff_one, ite_eq_right (Ne.symm hd), ite_eq_right hpd, base.map_zero]

/-- The polynomial splitting applies the coefficient splitting at exponents divisible
by the characteristic. -/
theorem polynomial_coeff [ExpChar R p] (base : RingSplitting R p) (hp : 0 < p)
    (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (base.polynomial hp f).coeff d = base (f.coeff (p • d)) := rfl

end FrobeniusSplitting.RingSplitting
