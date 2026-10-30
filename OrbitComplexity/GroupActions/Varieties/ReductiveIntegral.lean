import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.GroupActions.Varieties.Noetherian
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk

/-! # Integrality of reductive varieties

Smoothness makes the local rings of a reductive variety regular. Its connectedness then
implies irreducibility, and its reducedness gives integrality.

## Main results

* `GroupActions.reductiveVarietyIntegral`: the variety of a reductive group is integral.
-/

open AlgebraicGeometry

namespace GroupActions

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The variety of a reductive group is integral. -/
instance reductiveVarietyIntegral : IsIntegral (reductiveVariety G).scheme := by
  have : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  have : IsRegularRing G.coordinateAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (reductiveVariety G).scheme,
      IsRegularLocalRing ((reductiveVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.coordinateAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.coordinateAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

end GroupActions
