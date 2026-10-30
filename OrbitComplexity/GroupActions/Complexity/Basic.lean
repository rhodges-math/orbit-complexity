import OrbitComplexity.GroupActions.Varieties.BorelVariety
import OrbitComplexity.GroupActions.Complexity.DenseOrbits

/-! # Complexity of reductive group actions

The complexity of a reductive group action is the minimum codimension of an orbit of its
chosen Borel subgroup. The Borel action is the restriction of the original algebraic action.

## Main definitions

* `GroupActions.complexity`: minimum Borel orbit codimension of a reductive group action.

## Main results

* `GroupActions.complexity_isLeast`: complexity is the attained least integer orbit codimension.
* `GroupActions.complexity_eq_zero_iff_dense`: zero complexity is equivalent to a dense Borel orbit.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K) (X : Variety K)
  [ModObj (reductiveVariety G).toOver X.toOver]

/-- Complexity is the minimum codimension of an orbit of the chosen Borel subgroup. -/
def complexity : ℕ :=
  letI := Mod.scalarRestriction (borelInclusion G) X.toOver
  minOrbitCodim (borelVariety G) X

/-- Complexity is computed using the algebraic action restricted to the Borel subgroup. -/
theorem complexity_eq_minOrbitCodim :
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    complexity G X = minOrbitCodim (borelVariety G) X := rfl

/-- Complexity bounds the integer codimension of every Borel orbit. -/
theorem complexity_le (x : X.points) :
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    (complexity G X : ℤ) ≤ orbitCodim (borelVariety G) X x := by
  let := Mod.scalarRestriction (borelInclusion G) X.toOver
  exact minOrbitCodim_le (borelVariety G) X x

/-- Complexity is the least integer codimension of a Borel orbit on a nonempty variety. -/
theorem complexity_isLeast [Nonempty X.scheme] :
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    IsLeast (Set.range (orbitCodim (borelVariety G) X)) (complexity G X : ℤ) := by
  let := Mod.scalarRestriction (borelInclusion G) X.toOver
  exact minOrbitCodim_isLeast (borelVariety G) X

/-- Zero complexity on an irreducible variety is equivalent to a dense Borel orbit. -/
theorem complexity_eq_zero_iff_dense [IrreducibleSpace X.scheme] : complexity G X = 0 ↔
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    ∃ x : X.points, Dense (X.pointMap '' MulAction.orbit (borelVariety G).points x) := by
  let := Mod.scalarRestriction (borelInclusion G) X.toOver
  exact minOrbitCodim_eq_zero_iff (borelVariety G) X

end

end GroupActions
