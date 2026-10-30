import OrbitComplexity.GroupActions.Complexity.Basic

/-! # Minimum-codimension characterization of complexity

The algebraic Borel action computes complexity, and its integer orbit codimensions attain
their least value on an irreducible variety.

## Main results

* `GroupActions.complexity_definition`: complexity is the attained minimum Borel orbit
  codimension over an algebraically closed field of characteristic zero.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

universe u

/-- Complexity is the attained minimum integer codimension for the restricted Borel action. -/
@[nolint unusedArguments]
theorem complexity_definition {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (X : Variety K)
    [ModObj (reductiveVariety G).toOver X.toOver] [IrreducibleSpace X.scheme] :
    letI := Mod.scalarRestriction (borelInclusion G) X.toOver
    complexity G X = minOrbitCodim (borelVariety G) X ∧
      IsLeast (Set.range (orbitCodim (borelVariety G) X)) (complexity G X : ℤ) := by
  let := Mod.scalarRestriction (borelInclusion G) X.toOver
  exact ⟨complexity_eq_minOrbitCodim G X, complexity_isLeast G X⟩

end GroupActions
