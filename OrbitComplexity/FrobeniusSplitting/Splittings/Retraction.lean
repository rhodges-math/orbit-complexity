import OrbitComplexity.FrobeniusSplitting.Splittings.Basic

/-!
# Descent of splittings along module retractions

An algebra whose structure map admits a linear retraction taking one to one
carries a Frobenius splitting whenever the larger algebra does.

## Main definitions

* `FrobeniusSplitting.RingSplitting.descend`: descent through a linear retraction.

## Main results

* `FrobeniusSplitting.RingSplitting.descend_apply`: the formula for the descended splitting.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Lemma 1.1.9.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {p : ℕ}

/-- A linear retraction taking one to one carries a splitting to the base algebra. -/
def descend (splitting : RingSplitting S p) (retraction : S →ₗ[R] R)
    (hone : retraction 1 = 1) : RingSplitting R p where
  toAddMonoidHom := retraction.toAddMonoidHom.comp
    (splitting.toAddMonoidHom.comp (algebraMap R S).toAddMonoidHom)
  map_pow_mul' a b := by
    change retraction (splitting (algebraMap R S (a ^ p * b))) =
      a * retraction (splitting (algebraMap R S b))
    rw [(algebraMap R S).map_mul, (algebraMap R S).map_pow, splitting.map_pow_mul]
    rw [← Algebra.smul_def, retraction.map_smul, smul_eq_mul]
  map_one' := by
    change retraction (splitting (algebraMap R S 1)) = 1
    rw [(algebraMap R S).map_one, splitting.map_one, hone]

end FrobeniusSplitting.RingSplitting
