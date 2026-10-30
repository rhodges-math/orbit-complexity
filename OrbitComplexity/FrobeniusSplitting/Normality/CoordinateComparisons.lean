import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

/-!
# Affine coordinate comparison isomorphisms
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u v w

/-- The relative spectrum comparison of an affine scheme is an isomorphism. -/
theorem coordinates_unit_isIso (K : CommRingCat.{u}) (X : Over (Spec K))
    [IsAffine X.left] : IsIso ((algΓAlgSpecAdjunction K).unit.app X) := by
  exact (algΓAlgSpecAdjunction K).isIso_unit_app_iff_mem_essImage.mpr
    (essImage_algSpec.mpr inferInstance)

/-- An affine scheme diagram is naturally isomorphic to the spectra of its coordinates. -/
noncomputable def coordinateDiagramIso {C : Type v} [Category.{w} C]
    (K : CommRingCat.{u}) (D : C ⥤ Over (Spec K))
    [∀ i, IsAffine (D.obj i).left] : D ≅ D ⋙ algΓ K ⋙ algSpec K :=
  NatIso.ofComponents (fun i ↦ by
    have : IsIso ((algΓAlgSpecAdjunction K).unit.app (D.obj i)) :=
      coordinates_unit_isIso K (D.obj i)
    exact asIso ((algΓAlgSpecAdjunction K).unit.app (D.obj i)))
    (by
      intro i j f
      exact (algΓAlgSpecAdjunction K).unit.naturality (D.map f))

/-- Coordinate spectra preserve the open immersions of an affine scheme diagram. -/
theorem coordinateMaps_open {C : Type v} [Category.{w} C]
    (K : CommRingCat.{u}) (D : C ⥤ Over (Spec K)) [∀ i, IsAffine (D.obj i).left]
    (hopen : ∀ i j (f : i ⟶ j), IsOpenImmersion (D.map f).left)
    {i j : C} (f : i ⟶ j) :
    IsOpenImmersion ((D ⋙ algΓ K ⋙ algSpec K).map f).left := by
  let e := Functor.isoWhiskerRight (coordinateDiagramIso K D) (Over.forget (Spec K))
  have eArrow : Arrow.mk (D.map f).left ≅ Arrow.mk ((D ⋙ algΓ K ⋙ algSpec K).map f).left :=
    Arrow.isoMk (e.app i) (e.app j) (e.hom.naturality f).symm
  exact (MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion) eArrow).mp (hopen i j f)

/-- Coordinate spectra preserve cartesian squares of affine schemes over their base. -/
theorem coordinateSquare_pullback {C : Type v} [Category.{w} C]
    (K : CommRingCat.{u}) (D : C ⥤ Over (Spec K)) [∀ i, IsAffine (D.obj i).left]
    {i j k l : C} (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l)
    (h : CategoryTheory.IsPullback (D.map f).left (D.map g).left
      (D.map p).left (D.map q).left) :
    CategoryTheory.IsPullback ((D ⋙ algΓ K ⋙ algSpec K).map f).left
      ((D ⋙ algΓ K ⋙ algSpec K).map g).left
      ((D ⋙ algΓ K ⋙ algSpec K).map p).left
      ((D ⋙ algΓ K ⋙ algSpec K).map q).left := by
  let e := Functor.isoWhiskerRight (coordinateDiagramIso K D) (Over.forget (Spec K))
  exact h.of_iso (e.app i) (e.app j) (e.app k) (e.app l)
    (e.hom.naturality f) (e.hom.naturality g) (e.hom.naturality p) (e.hom.naturality q)

end FrobeniusSplitting
