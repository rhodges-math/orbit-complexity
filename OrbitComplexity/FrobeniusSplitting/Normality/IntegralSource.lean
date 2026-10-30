import OrbitComplexity.FrobeniusSplitting.Normality.Proper
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk

/-!
# Integral sources of proper morphisms with connected fibers

A proper morphism with geometrically connected fibers has connected source when its target is
connected. Domain stalks then give irreducibility for a locally Noetherian source. A smooth source
therefore satisfies the integrality hypothesis in the proper normality criterion automatically.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory

/-- A proper morphism with geometrically connected fibers over a connected scheme
has connected source. -/
theorem connectedSpace_of_proper {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    [GeometricallyConnected f] [ConnectedSpace Y] : ConnectedSpace X := by
  have hq := (f.isClosedMap.isQuotientMap f.continuous f.surjective).isCoinducing
  rw [connectedSpace_iff_univ]
  simpa only [Set.preimage_univ] using hq.isConnected_preimage_of_isClosed
    f.isConnected_preimage_singleton isClosed_univ isConnected_univ

/-- A locally Noetherian source with domain stalks is integral if it maps properly
with geometrically connected fibers to a connected scheme. -/
theorem isIntegral_of_proper {X Y : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Y)
    [IsProper f] [GeometricallyConnected f] [ConnectedSpace Y]
    (hd : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  have : ConnectedSpace X := connectedSpace_of_proper f
  have : IrreducibleSpace X :=
    TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk X hd
  have (x : X) : IsDomain (X.presheaf.stalk x) := hd x
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

universe u

end FrobeniusSplitting
