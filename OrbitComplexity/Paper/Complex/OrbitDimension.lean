import OrbitComplexity.GroupActions.Actions.OrbitDimensionGeneral
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Orbit dimension over the complex numbers

Orbits of a complex algebraic group are locally closed, with dimension equal to the
group dimension minus the stabilizer dimension.

## Main results

* `orbit_dimension_complex`: local closedness and the dimension formula over the complex numbers.

## References

* M. Brion, *Introduction to actions of algebraic groups*, Luminy lecture notes (2009),
  Proposition 1.11.
-/

open CategoryTheory GroupActions

namespace SchubertOrbits

/-- A complex algebraic group orbit is locally closed and has dimension equal to the group
dimension minus its stabilizer dimension. -/
theorem orbit_dimension_complex (H X : Variety ℂ) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (x : X.points) :
    IsLocallyClosed (MulAction.orbit H.points x) ∧
      (orbitNatDim H X x : ℤ) = (H.natDim : ℤ) -
        ((stabilizerVariety H X x).natDim : ℤ) :=
  GroupActions.orbit_dimension_formula H X x

end SchubertOrbits
