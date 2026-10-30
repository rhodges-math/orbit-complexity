import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Tori.LaurentDimension
import OrbitComplexity.GroupActions.Varieties.TorusVariety
import OrbitComplexity.GroupActions.Varieties.FiniteDimension

/-! # Dimension of the chosen maximal torus

The splitting identifies the coordinate algebra of the chosen torus with the group algebra
of its character lattice. Its dimension is therefore the rank of that lattice.

## Main results

* `GroupActions.torusVariety_dim`: the torus dimension equals its character-lattice rank.
-/

open AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The chosen maximal torus has dimension equal to its character-lattice rank. -/
theorem torusVariety_dim : (torusVariety G).dim = (Nat.card G.torusIndex : WithBot ℕ∞) := by
  let := G.finiteIndex
  calc
    (torusVariety G).dim = ringKrullDim G.torusAlgebra :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = ringKrullDim (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ))) :=
      ringKrullDim_eq_of_ringEquiv (torusCoordinateEquiv G).toRingEquiv
    _ = (Nat.card G.torusIndex : WithBot ℕ∞) := ringKrullDim_splitTorus K G.torusIndex

end

end GroupActions
