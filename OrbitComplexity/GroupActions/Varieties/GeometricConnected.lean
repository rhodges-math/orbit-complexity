import Mathlib.AlgebraicGeometry.Geometrically.Connected
import TauCeti.RingTheory.Idempotents.Connected.ScalarExtension

/-! # Connected schemes over algebraically closed fields

Connected affine algebras remain connected under field extension. Applying this to the
extending field makes the base-change projection geometrically connected and open, so
connectedness is preserved for arbitrary schemes over an algebraically closed field.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct
namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem affine_geo_connected
    (A : Type u) [CommRing A] [Algebra K A] [ConnectedSpace (PrimeSpectrum A)] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X => ConnectedSpace X)).mpr ?_⟩
  intro L _ _
  have ht : ConnectedSpace (PrimeSpectrum (A ⊗[K] L)) :=
    TauCeti.connectedSpace_primeSpectrum_tensorProduct_of_isAlgClosed K A L
  exact (pullbackSpecIso K A L).hom.homeomorph.connectedSpace_iff.mpr ht

private theorem field_extension_geoConnected {L : Type u} [Field L]
    (y : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    GeometricallyConnected y := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact affine_geo_connected L

/-- A connected scheme over an algebraically closed field is geometrically connected. -/
theorem geometricallyConnected_of_algClosed {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of K)) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ y
  have : GeometricallyConnected y := field_extension_geoConnected y
  infer_instance

end
end GroupActions
