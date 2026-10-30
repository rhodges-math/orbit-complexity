import OrbitComplexity.SchubertGeometry.Connectedness.PairedModelIntegral
import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Integral field fibres of a smooth connected family

A smooth geometrically connected family has integral field fibres with
domain and integrally closed stalks. This formulation uses the structural
map of a single model and is preserved when coefficient stages are combined.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace SchubertGeometry

open private integral_field_fibres
  from OrbitComplexity.SchubertGeometry.Connectedness.PairedModelIntegral
open private iso_gc
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

/-- A smooth geometrically connected model has integral field fibres,
each with domain and integrally closed stalks. -/
theorem integral_smooth_field_fibres {B : Scheme.{u}}
    (C : Over B) [Smooth C.hom] [GeometricallyConnected C.hom]
    (L : Type u) [Field L] (s : Spec (.of L) ⟶ B) :
    IsIntegral (pullback s C.hom : Scheme.{u}) ∧
      ∀ x : (pullback s C.hom : Scheme.{u}),
        IsDomain ((pullback s C.hom : Scheme.{u}).presheaf.stalk x) ∧
        IsIntegrallyClosed ((pullback s C.hom : Scheme.{u}).presheaf.stalk x) := by
  let e : C ⟶ C := 𝟙 C
  let : IsProper e.left := by
    change IsProper (𝟙 C.left)
    infer_instance
  let : GeometricallyConnected e.left := by
    change GeometricallyConnected (𝟙 C.left)
    exact iso_gc _
  exact integral_field_fibres e L s

end SchubertGeometry
