import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Frobenius splittings of perfect rings

The inverse of the Frobenius automorphism splits a perfect ring. Surjectivity of
Frobenius implies that this is the only splitting.

## Main definitions

* `FrobeniusSplitting.RingSplitting.ofPerfectRing`: the inverse Frobenius splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.eq_of_perfect`: uniqueness over a perfect ring.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Remark 1.1.4.
-/

namespace FrobeniusSplitting.RingSplitting

variable (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p] [PerfectRing R p]

/-- The inverse Frobenius automorphism is a splitting of a perfect ring. -/
noncomputable def ofPerfectRing : RingSplitting R p where
  toAddMonoidHom := (frobeniusEquiv R p).symm.toAddMonoidHom
  map_pow_mul' a b := by
    change (frobeniusEquiv R p).symm (a ^ p * b) =
      a * (frobeniusEquiv R p).symm b
    rw [(frobeniusEquiv R p).symm.map_mul]
    change (frobeniusEquiv R p).symm (frobeniusEquiv R p a) * _ = _
    rw [(frobeniusEquiv R p).symm_apply_apply]
  map_one' := (frobeniusEquiv R p).symm.map_one

/-- The perfect-ring splitting evaluates by inverse Frobenius. -/
theorem ofPerfectRing_apply (a : R) :
    ofPerfectRing R p a = (frobeniusEquiv R p).symm a :=
  rfl

/-- A perfect ring has only the inverse Frobenius splitting. -/
theorem eq_of_perfect (splitting : RingSplitting R p) :
    splitting = ofPerfectRing R p := by
  ext a
  obtain ⟨b, rfl⟩ := surjective_frobenius R p a
  change splitting (b ^ p) = ofPerfectRing R p (b ^ p)
  rw [splitting.map_pow, (ofPerfectRing R p).map_pow]

end FrobeniusSplitting.RingSplitting
