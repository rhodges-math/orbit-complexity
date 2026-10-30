import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitProperties
import OrbitComplexity.FrobeniusSplitting.Normality.BundleProperties

/-!
# ComponentBundles

Mixed affine diagrams and geometric properties of their colimit morphisms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- Proper smooth projections with connected geometric fibres glue along an
equifibered open diagram to a morphism with the same three properties. -/
theorem bundle_properties_of_components {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F G : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⟶ G) (hα : α.Equifibered)
    [∀ i, IsProper (α.app i)] [∀ i, Smooth (α.app i)]
    [∀ i, GeometricallyConnected (α.app i)]
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hcomp : ∀ i, cF.ι.app i ≫ q = α.app i ≫ cG.ι.app i) :
    IsProper q ∧ Smooth q ∧ GeometricallyConnected q := by
  have hproper : IsProper q := property_of_colimit_components @IsProper
    F G α hα cF cG hcF hcG q hcomp (fun _ ↦ inferInstance)
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u})
  have hsmooth : Smooth q := property_of_colimit_components @Smooth
    F G α hα cF cG hcF hcG q hcomp (fun _ ↦ inferInstance)
  have hconn : geometrically (ConnectedSpace ·) q :=
    property_of_colimit_components (geometrically (ConnectedSpace ·))
      F G α hα cF cG hcF hcG q hcomp
      (fun i ↦ GeometricallyConnected.geometrically_connectedSpace (f := α.app i))
  exact ⟨hproper, hsmooth, ⟨hconn⟩⟩

end FrobeniusSplitting
