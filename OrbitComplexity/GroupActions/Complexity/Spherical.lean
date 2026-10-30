import OrbitComplexity.GroupActions.Complexity.Basic
import OrbitComplexity.GroupActions.Varieties.Normal

/-! # Spherical varieties

A normal irreducible variety with a reductive group action is spherical when its complexity
is zero. Equivalently, it has a dense orbit of the chosen Borel subgroup.

## Main definitions

* `GroupActions.IsSpherical`: normality and vanishing complexity.

## Main results

* `GroupActions.isSpherical_iff_normal_dense`: sphericality is equivalent to normality and a
  dense Borel orbit.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K) (X : Variety K)
  [ModObj (reductiveVariety G).toOver X.toOver]

/-- A normal irreducible variety with zero reductive-group complexity is spherical. -/
def IsSpherical : Prop := IrreducibleSpace X.scheme ∧ X.IsNormal ∧ complexity G X = 0

/-- Sphericality is equivalent to normality and existence of a dense Borel orbit. -/
theorem isSpherical_iff_normal_dense [IrreducibleSpace X.scheme] :
    IsSpherical G X ↔ X.IsNormal ∧
      letI := Mod.scalarRestriction (borelInclusion G) X.toOver
      ∃ x : X.points, Dense (X.pointMap '' MulAction.orbit (borelVariety G).points x) := by
  rw [IsSpherical, complexity_eq_zero_iff_dense]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩

end GroupActions
