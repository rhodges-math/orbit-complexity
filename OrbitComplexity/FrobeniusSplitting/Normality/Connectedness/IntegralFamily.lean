import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Properties
import Batteries.Tactic.Lint

/-! # Connectedness of families with integral field fibres

Integral fibres after every field extension give geometric connectedness.
An isomorphism over a fixed base preserves this property of structural maps.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace FrobeniusSplitting

/-- Integral fibres over every field imply geometric connectedness. -/
theorem geomConnected_of_integral_fibres {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (h : ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Y),
      IsIntegral (pullback s f : Scheme.{u})) :
    GeometricallyConnected f := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro L _ s
  let : IsIntegral (pullback s f : Scheme.{u}) := h L s
  let : IsIntegral (pullback f s : Scheme.{u}) :=
    IsIntegral.of_isIso (pullbackSymmetry s f).hom
  infer_instance

/-- An isomorphism over a fixed base preserves geometric connectedness
of the structural map. -/
theorem geomConnected_over_iso {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) (h : GeometricallyConnected X.hom) :
    GeometricallyConnected Y.hom := by
  have hcart : IsPullback E.inv.left Y.hom X.hom (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using E.inv.w⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hcart h

end FrobeniusSplitting
