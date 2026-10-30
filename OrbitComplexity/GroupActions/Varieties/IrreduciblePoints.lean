import OrbitComplexity.GroupActions.Varieties.Basic
import Mathlib.Topology.Irreducible

/-! # Irreducibility of rational points

Rational points are dense in a variety over an algebraically closed field, and their
induced Zariski topology preserves irreducibility.
-/

open AlgebraicGeometry Topology

namespace GroupActions.Variety

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (X : GroupActions.Variety K)

/-- Rational points of an irreducible variety form an irreducible topological space. -/
instance pointsIrreducible [IrreducibleSpace X.scheme] : IrreducibleSpace X.points := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  have hc : closure (Set.range X.pointMap) = Set.univ := by
    rw [X.pointMap_range, closure_closedPoints]
  have hi : IsIrreducible (Set.range X.pointMap) :=
    isIrreducible_iff_closure.mp (hc.symm ▸ IrreducibleSpace.isIrreducible_univ X.scheme)
  have : IrreducibleSpace (Set.range X.pointMap) := Subtype.irreducibleSpace hi
  exact X.isEmbedding_pointMap.toHomeomorph.irreducibleSpace_iff.mpr inferInstance

end GroupActions.Variety