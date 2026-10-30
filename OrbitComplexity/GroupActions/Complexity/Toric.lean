import OrbitComplexity.GroupActions.Varieties.TorusVariety
import OrbitComplexity.GroupActions.Varieties.Normal
import OrbitComplexity.GroupActions.Complexity.DenseOrbits

/-! # Torus complexity and toric varieties

Torus complexity is the minimum codimension of an orbit of the chosen maximal torus. The
action is given on the torus itself and need not extend to the ambient reductive group.
A normal irreducible torus variety is toric when its torus complexity vanishes.

## Main definitions

* `GroupActions.torusComplexity`: minimum codimension of a torus orbit.
* `GroupActions.IsToricVariety`: normality and zero torus complexity.

## Main results

* `GroupActions.isToricVariety_iff_normal_dense`: toricity is equivalent to normality and a dense
  torus orbit.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K) (X : Variety K)
  [ModObj (torusVariety G).toOver X.toOver]

/-- Torus complexity is the minimum codimension of an orbit of the chosen maximal torus. -/
def torusComplexity : ℕ := minOrbitCodim (torusVariety G) X

/-- Torus complexity bounds every integer torus orbit codimension. -/
theorem torusComplexity_le (x : X.points) :
    (torusComplexity G X : ℤ) ≤ orbitCodim (torusVariety G) X x :=
  minOrbitCodim_le (torusVariety G) X x

/-- Torus complexity is the least integer torus orbit codimension. -/
theorem torusComplexity_isLeast [IsAlgClosed K] [Nonempty X.scheme] :
    IsLeast (Set.range (orbitCodim (torusVariety G) X)) (torusComplexity G X : ℤ) :=
  minOrbitCodim_isLeast (torusVariety G) X

/-- Zero torus complexity is equivalent to the existence of a scheme-dense torus orbit. -/
theorem torusComplexity_eq_zero_iff [IsAlgClosed K] [IrreducibleSpace X.scheme] :
    torusComplexity G X = 0 ↔
      ∃ x : X.points, Dense (X.pointMap '' MulAction.orbit (torusVariety G).points x) :=
  minOrbitCodim_eq_zero_iff (torusVariety G) X

/-- A normal irreducible torus variety with zero torus complexity is toric. -/
def IsToricVariety : Prop := IrreducibleSpace X.scheme ∧ X.IsNormal ∧ torusComplexity G X = 0

/-- Toricity is equivalent to normality and existence of a scheme-dense torus orbit. -/
theorem isToricVariety_iff_normal_dense [IsAlgClosed K] [IrreducibleSpace X.scheme] :
    IsToricVariety G X ↔ X.IsNormal ∧
      ∃ x : X.points, Dense (X.pointMap '' MulAction.orbit (torusVariety G).points x) := by
  rw [IsToricVariety, torusComplexity_eq_zero_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩

end

end GroupActions
