import OrbitComplexity.GroupActions.Actions.Points
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.CategoryTheory.Endomorphism

/-! # Orbit morphisms and translations

The orbit map of a rational point is a morphism over the base field. Translation by a
rational group element is an automorphism of the variety.

## Main definitions

* `GroupActions.Variety.orbitMorphism`: the orbit morphism of a rational point.
* `GroupActions.Variety.translateMorphism`: translation by a rational group element.

## Main results

* `GroupActions.Variety.mapPoints_orbitMorphism`: the orbit morphism acts by the group action.
* `GroupActions.Variety.mapPoints_translateMorphism`: translation acts by the group action.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

private theorem toUnit_base (S : Scheme.{u}) :
    toUnit (Over.mk (𝟙 S)) = 𝟙 (Over.mk (𝟙 S)) := toUnit_unique _ _

variable {K : Type u} [Field K] (H X : GroupActions.Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The orbit morphism sends a group element to its action on a fixed rational point. -/
def orbitMorphism (x : X.points) : H.toOver ⟶ X.toOver :=
  lift (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x) ≫
    ModObj.smul (M := H.toOver) (X := X.toOver)

/-- On rational points the orbit morphism agrees with the group action. -/
theorem mapPoints_orbitMorphism (x : X.points) (h : H.points) :
    mapPoints (orbitMorphism H X x) h = h • x := by
  apply X.pointsEquivOverHom.injective
  rw [pointsEquivOverHom_smul]
  change H.pointsEquivOverHom h ≫ orbitMorphism H X x =
    H.pointsEquivOverHom h • X.pointsEquivOverHom x
  simp only [orbitMorphism, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc,
    toUnit_base, Category.id_comp, CategoryTheory.Hom.smul_def]

/-- The image on rational points of the orbit morphism is the orbit. -/
theorem range_orbitMorphism (x : X.points) :
    Set.range (mapPoints (orbitMorphism H X x)) = MulAction.orbit H.points x := by
  rw [show mapPoints (orbitMorphism H X x) = (fun h : H.points ↦ h • x) from
    funext (mapPoints_orbitMorphism H X x)]
  rfl

/-- Translation by a rational group element as a morphism over the base field. -/
def translateMorphism (h : H.points) : X.toOver ⟶ X.toOver :=
  (toUnit X.toOver ≫ H.pointsEquivOverHom h) • 𝟙 X.toOver

/-- Translation by a rational point acts on rational points by the group action. -/
theorem mapPoints_translateMorphism (h : H.points) (x : X.points) :
    mapPoints (translateMorphism H X h) x = h • x := by
  apply X.pointsEquivOverHom.injective
  rw [pointsEquivOverHom_smul]
  change X.pointsEquivOverHom x ≫ translateMorphism H X h =
    H.pointsEquivOverHom h • X.pointsEquivOverHom x
  rw [translateMorphism, ModObj.comp_smul]
  simp only [comp_toUnit_assoc, toUnit_base, Category.id_comp, Category.comp_id]

/-- Composing translations reverses the order in the displayed product. -/
theorem translateMorphism_comp (h k : H.points) :
    translateMorphism H X h ≫ translateMorphism H X k = translateMorphism H X (k * h) := by
  simp only [translateMorphism, ModObj.comp_smul, comp_toUnit_assoc,
    Category.comp_id, ← mul_smul, ← MonObj.comp_mul, pointsEquivOverHom_mul]

/-- Translation by the identity group element is the identity morphism. -/
theorem translateMorphism_one : translateMorphism H X 1 = 𝟙 X.toOver := by
  simp only [translateMorphism, pointsEquivOverHom_one, MonObj.comp_one, one_smul]

/-- Translation by a rational group element is an isomorphism of varieties. -/
def translationIso (h : H.points) : X.toOver ≅ X.toOver where
  hom := translateMorphism H X h
  inv := translateMorphism H X h⁻¹
  hom_inv_id := by rw [translateMorphism_comp, inv_mul_cancel, translateMorphism_one]
  inv_hom_id := by rw [translateMorphism_comp, mul_inv_cancel, translateMorphism_one]

/-- Rational group elements act by automorphisms over the base field. -/
def translationHom : H.points →* Aut X.toOver where
  toFun := translationIso H X
  map_one' := by
    apply Iso.ext
    exact translateMorphism_one H X
  map_mul' h k := by
    apply Iso.ext
    exact (translateMorphism_comp H X k h).symm

/-- Rational group elements act by automorphisms of the underlying scheme. -/
def schemeTranslationHom : H.points →* Aut X.scheme :=
  ((Over.forget _).mapAut X.toOver).comp (translationHom H X)

/-- The scheme automorphism of a rational group element is its translation morphism. -/
theorem schemeTranslationHom_hom (h : H.points) :
    (schemeTranslationHom H X h).hom = (translateMorphism H X h).left := rfl

end

end GroupActions.Variety
