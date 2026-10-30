import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Coordinates on the chosen split torus

The splitting map identifies the coordinate algebra of the chosen maximal torus with the
group algebra of its free character lattice.

## Main definitions

* `GroupActions.torusCoordinateEquiv`: the splitting as an isomorphism of coordinate algebras.
-/

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The coordinate algebra of the chosen maximal torus is the group algebra of its lattice. -/
def torusCoordinateEquiv : G.torusAlgebra ≃ₐ[K]
    MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) := by
  have hker : G.torusIdeal.toIdeal = RingHom.ker G.torusSplit.toAlgHom.toRingHom := by
    ext a
    exact (G.split_eq_zero a).symm
  exact (Ideal.quotientEquivAlgOfEq K hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := G.torusSplit.toAlgHom) G.split_surjective)

/-- The splitting isomorphism evaluates a quotient coordinate by the original splitting map. -/
theorem torusCoordinateEquiv_mk (a : G.coordinateAlgebra) :
    torusCoordinateEquiv G (Ideal.Quotient.mk G.torusIdeal.toIdeal a) = G.torusSplit a := rfl

end

end GroupActions
