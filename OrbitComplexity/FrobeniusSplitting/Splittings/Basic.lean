import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Frobenius splittings of commutative semirings

A Frobenius splitting is an additive retraction of the Frobenius map satisfying
the Frobenius linearity identity. A splitting in characteristic greater than one
forces the semiring to be reduced.

## Main definitions

* `FrobeniusSplitting.RingSplitting`: additive Frobenius-linear maps taking one to one.

## Main results

* `FrobeniusSplitting.RingSplitting.left_inverse`: a splitting retracts Frobenius.
* `FrobeniusSplitting.RingSplitting.isReduced`: a split semiring is reduced.

## Implementation notes

Power linearity also applies to the zero ring and to rings of sections on an empty
open subset. The exponential characteristic is used when expressing the retraction
through the Frobenius ring homomorphism.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Definition 1.1.3,
  Remark 1.1.4 and Proposition 1.2.1.
-/

namespace FrobeniusSplitting

variable (R : Type*) [CommSemiring R] (p : ℕ)

/-- An additive Frobenius-linear map taking one to one. -/
structure RingSplitting where
  /-- The underlying additive map. -/
  toAddMonoidHom : R →+ R
  /-- Frobenius linearity with respect to multiplication. -/
  map_pow_mul' (a b : R) : toAddMonoidHom (a ^ p * b) = a * toAddMonoidHom b
  /-- The splitting takes one to one. -/
  map_one' : toAddMonoidHom 1 = 1

namespace RingSplitting

/-- A ring splitting acts on elements through its additive map. -/
instance : CoeFun (RingSplitting R p) (fun _ ↦ R → R) :=
  ⟨fun splitting ↦ splitting.toAddMonoidHom⟩

variable {R p}

/-- Splittings with the same values on every element are equal. -/
@[ext]
theorem ext {splitting other : RingSplitting R p}
    (heq : ∀ a, splitting a = other a) : splitting = other := by
  cases splitting
  cases other
  congr
  exact AddMonoidHom.ext heq

/-- A splitting takes zero to zero. -/
@[simp]
theorem map_zero (splitting : RingSplitting R p) : splitting 0 = 0 :=
  splitting.toAddMonoidHom.map_zero

/-- A splitting preserves addition. -/
theorem map_add (splitting : RingSplitting R p) (a b : R) :
    splitting (a + b) = splitting a + splitting b :=
  splitting.toAddMonoidHom.map_add a b

/-- A splitting takes one to one. -/
@[simp]
theorem map_one (splitting : RingSplitting R p) : splitting 1 = 1 :=
  splitting.map_one'

/-- Frobenius linearity can be expressed using powers. -/
theorem map_pow_mul (splitting : RingSplitting R p) (a b : R) :
    splitting (a ^ p * b) = a * splitting b :=
  splitting.map_pow_mul' a b

/-- A splitting satisfies the Frobenius linearity identity. -/
theorem map_frobenius_mul [ExpChar R p] (splitting : RingSplitting R p) (a b : R) :
    splitting (frobenius R p a * b) = a * splitting b :=
  splitting.map_pow_mul a b

/-- A splitting maps the `p`-th power of an element to that element. -/
@[simp]
theorem map_pow (splitting : RingSplitting R p) (a : R) :
    splitting (a ^ p) = a := by
  simpa only [mul_one, splitting.map_one] using splitting.map_pow_mul a 1

/-- A splitting is a left inverse of the Frobenius endomorphism. -/
theorem left_inverse [ExpChar R p] (splitting : RingSplitting R p) :
    Function.LeftInverse splitting (frobenius R p) :=
  splitting.map_pow

/-- A semiring with a Frobenius splitting of exponent greater than one is reduced. -/
theorem isReduced (splitting : RingSplitting R p) (hp : 1 < p) : IsReduced R := by
  apply (isReduced_iff_pow_one_lt p hp).2
  intro a hpow
  calc
    a = splitting (a ^ p) := (splitting.map_pow a).symm
    _ = 0 := hpow ▸ splitting.map_zero

end RingSplitting

end FrobeniusSplitting
