import OrbitComplexity.FrobeniusSplitting.Splittings.LinearMap
import OrbitComplexity.FrobeniusSplitting.Splittings.Polynomial

/-!
# Polynomial Cartier trace

The Cartier trace extracts coefficients whose exponents in every variable are congruent to
minus one modulo the characteristic. Weighting this operator by the top monomial gives the
canonical polynomial splitting.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Section 1.3.
-/

namespace FrobeniusSplitting

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p : ℕ}

/-- The exponent with every coordinate equal to the characteristic minus one. -/
noncomputable def traceDegree (σ : Type*) [Finite σ] (p : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ ↦ p - 1)

/-- Every coordinate of the trace exponent is the characteristic minus one. -/
@[simp]
theorem traceDegree_apply [Finite σ] (i : σ) : traceDegree σ p i = p - 1 := by
  simp [traceDegree]

private theorem traceExponent_injective [Finite σ] (hp : 0 < p) :
    Function.Injective (fun d : σ →₀ ℕ ↦ p • d + traceDegree σ p) := by
  intro a b h
  exact (nsmul_right_inj hp.ne_zero).1 (add_right_cancel h)

private noncomputable def traceMap [Finite σ] (base : RingSplitting R p) (hp : 0 < p) :
    MvPolynomial σ R →+ MvPolynomial σ R where
  toFun f := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange base base.map_zero
    (Finsupp.comapDomain (fun d : σ →₀ ℕ ↦ p • d + traceDegree σ p)
      (AddMonoidAlgebra.coeff f) (traceExponent_injective hp).injOn))
  map_zero' := by
    ext d
    exact base.map_zero
  map_add' f g := by
    ext d
    exact base.map_add (f.coeff (p • d + traceDegree σ p))
      (g.coeff (p • d + traceDegree σ p))

private theorem traceMap_coeff [Finite σ] (base : RingSplitting R p) (hp : 0 < p)
    (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (traceMap base hp f).coeff d = base (f.coeff (p • d + traceDegree σ p)) := rfl

private theorem traceExponent_le [Finite σ] (hp : 0 < p) (a d : σ →₀ ℕ) :
    p • a ≤ p • d + traceDegree σ p ↔ a ≤ d := by
  simp only [Finsupp.le_def, Finsupp.smul_apply, Finsupp.add_apply, traceDegree_apply,
    smul_eq_mul]
  constructor
  · intro h i
    by_contra hn
    have hi : d i + 1 ≤ a i := by omega
    have hmul := Nat.mul_le_mul_left p hi
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hbound := h i
    omega
  · intro h i
    have hi := Nat.mul_le_mul_left p (h i)
    omega

private theorem traceExponent_sub [Finite σ] (a d : σ →₀ ℕ)
    (had : a ≤ d) :
    p • d + traceDegree σ p - p • a = p • (d - a) + traceDegree σ p := by
  ext i
  simp only [Finsupp.tsub_apply, Finsupp.smul_apply, Finsupp.add_apply, traceDegree_apply,
    smul_eq_mul]
  have hi := Nat.mul_le_mul_left p (had i)
  rw [Nat.add_comm (p * d i), Nat.add_sub_assoc hi, ← Nat.mul_sub_left_distrib,
    Nat.add_comm]

private theorem traceMap_monomial [Finite σ] (base : RingSplitting R p) (hp : 0 < p)
    (a : σ →₀ ℕ) (r : R) (g : MvPolynomial σ R) :
    traceMap base hp ((monomial a r) ^ p * g) = monomial a r * traceMap base hp g := by
  classical
  ext d
  rw [traceMap_coeff, monomial_pow, coeff_monomial_mul', coeff_monomial_mul']
  by_cases h : a ≤ d
  · rw [ite_eq_left ((traceExponent_le hp a d).2 h), ite_eq_left h,
      traceExponent_sub a d h, base.map_pow_mul, traceMap_coeff]
  · rw [ite_eq_right ((traceExponent_le hp a d).not.2 h), ite_eq_right h, base.map_zero]

/-- The polynomial Cartier trace extracts exponents congruent to minus one. -/
noncomputable def polynomialTrace [ExpChar R p] [Finite σ]
    (base : RingSplitting R p) (hp : 0 < p) : FrobeniusLinearMap (MvPolynomial σ R) p where
  toAddMonoidHom := traceMap base hp
  map_pow_mul' a b := by
    change traceMap base hp (a ^ p * b) = a * traceMap base hp b
    refine MvPolynomial.induction_on' a (fun d r ↦ traceMap_monomial base hp d r b) ?_
    intro f g hf hg
    rw [add_pow_expChar, add_mul, (traceMap base hp).map_add, hf, hg, add_mul]

/-- Each Cartier-trace coefficient is obtained from the corresponding shifted exponent. -/
theorem polynomialTrace_coeff [ExpChar R p] [Finite σ]
    (base : RingSplitting R p) (hp : 0 < p) (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (polynomialTrace base hp f).coeff d = base (f.coeff (p • d + traceDegree σ p)) := rfl

/-- Weighting the Cartier trace by the top monomial gives the polynomial splitting. -/
theorem polynomialTrace_weight [ExpChar R p] [Finite σ]
    (base : RingSplitting R p) (hp : 0 < p) (f : MvPolynomial σ R) :
    polynomialTrace base hp (monomial (traceDegree σ p) 1 * f) =
      base.polynomial hp f := by
  classical
  ext d
  rw [polynomialTrace_coeff, RingSplitting.polynomial_coeff, coeff_monomial_mul']
  have hle : traceDegree σ p ≤ p • d + traceDegree σ p := le_add_self
  rw [ite_eq_left hle, one_mul, add_tsub_cancel_right]

/-- The Cartier trace of the top monomial is one. -/
theorem polynomialTrace_monomial [ExpChar R p] [Finite σ]
    (base : RingSplitting R p) (hp : 0 < p) :
    polynomialTrace base hp (monomial (traceDegree σ p) 1) = 1 := by
  simpa only [mul_one, RingSplitting.map_one] using polynomialTrace_weight base hp 1

/-- The weighted Cartier-trace splitting equals the canonical polynomial splitting. -/
theorem polynomialTrace_toSplitting [ExpChar R p] [Finite σ]
    (base : RingSplitting R p) (hp : 0 < p) :
    (polynomialTrace base hp).toSplitting (monomial (traceDegree σ p) 1)
      (polynomialTrace_monomial base hp) = base.polynomial hp := by
  apply RingSplitting.ext
  intro f
  exact polynomialTrace_weight base hp f

end FrobeniusSplitting
