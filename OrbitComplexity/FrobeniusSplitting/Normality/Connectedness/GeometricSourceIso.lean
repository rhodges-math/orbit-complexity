import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Geometric connectedness after a source isomorphism

An isomorphism of the source supplies a Cartesian square over the identity
of the target. Base-change stability transports geometric connectedness
directly, without an additional morphism-property class identification.
-/

open AlgebraicGeometry CategoryTheory

namespace FrobeniusSplitting

universe u

/-- Precomposing a geometrically connected map by a source isomorphism
preserves its connected geometric fibres. -/
theorem geomConnected_comp_iso {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z)
    [GeometricallyConnected f] : GeometricallyConnected (e.hom ≫ f) := by
  have h : IsPullback e.hom (e.hom ≫ f) f (𝟙 Z) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id]⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) h inferInstance

end FrobeniusSplitting
