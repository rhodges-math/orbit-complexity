import OrbitComplexity.GroupActions.Complexity.Definition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complexity over the complex numbers

Complexity is the minimum integer codimension of an orbit of the chosen Borel subgroup,
acting by restriction of the reductive group action.

## Main results

* `complexity_complex`: the defining minimum for a complex reductive group variety.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  arXiv:2405.13774v2, Definition 1.1.
-/

open CategoryTheory GroupActions

namespace SchubertOrbits

/-- Complexity of an irreducible complex reductive group variety is its least Borel orbit
codimension. -/
theorem complexity_complex (G : ReductiveGroups.ReductiveGroupData ℂ) (X : Variety ℂ)
    [ModObj (reductiveVariety G).toOver X.toOver] [IrreducibleSpace X.scheme] :
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    complexity G X = minOrbitCodim (borelVariety G) X ∧
    IsLeast (Set.range (orbitCodim (borelVariety G) X)) (complexity G X : ℤ) :=
  GroupActions.complexity_definition G X

end SchubertOrbits
