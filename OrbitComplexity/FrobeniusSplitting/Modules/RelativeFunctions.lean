import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Relative regular functions and identity-section pullback -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable (S : Scheme.{u})

/-- Functions on the original inverse-image scheme, with its base-module structure. -/
def relativeFunctionsObj (X : Over S) : S.Modules :=
  (Scheme.Modules.pushforward X.hom).obj (SheafOfModules.unit X.left.ringCatSheaf)

/-- A morphism over the same base pulls back regular functions. -/
def relativeFunctionsMap {X Y : Over S} (f : X ⟶ Y) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsObj S Y ⟶
        FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X :=
  (Scheme.Modules.pushforward Y.hom).map
      (SheafOfModules.unitToPushforwardObjUnit f.left.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp f.left Y.hom).hom.app
        (SheafOfModules.unit X.left.ringCatSheaf) ≫
      (Scheme.Modules.pushforwardCongr f.w).hom.app
        (SheafOfModules.unit X.left.ringCatSheaf)

private theorem overPreimage {X Y : Over S} (f : X ⟶ Y) (V : S.Opens) :
    X.hom ⁻¹ᵁ V ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ V) := by
  change X.hom ⁻¹ᵁ V ≤ (f.left ≫ Y.hom) ⁻¹ᵁ V
  rw [f.w]

/-- On every open the relative pullback is the scheme map on regular functions. -/
theorem relativeFunctionsMap_app {X Y : Over S} (f : X ⟶ Y) (V : S.Opens)
    (s : Γ(Y.left, Y.hom ⁻¹ᵁ V)) :
    ((FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f).val.app (.op V)).hom s =
      f.left.appLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.overPreimage S f
          V) s := by
  rfl

private theorem relativeFunctionsMap_id (X : Over S) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (𝟙 X) = 𝟙
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X) := by
  ext V s
  change ((FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (𝟙 X)).val.app (.op V)).hom s = s
  erw [FrobeniusSplitting.CharacterLine.relativeFunctionsMap_app S (𝟙 X) V]
  have hi : (homOfLE (FrobeniusSplitting.CharacterLine.overPreimage S (𝟙 X) V)).op =
      𝟙 (Opposite.op (X.hom ⁻¹ᵁ V)) := Subsingleton.elim _ _
  simp only [Over.id_left, Scheme.Hom.appLE]
  rw [hi]
  exact ConcreteCategory.congr_hom
    ((Category.id_comp _).trans
      (CategoryTheory.Functor.map_id X.left.presheaf
        (Opposite.op (X.hom ⁻¹ᵁ V)))) s

private theorem relativeFunctionsMap_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (f ≫ g) =
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S g ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f := by
  ext V s
  change ((FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (f ≫ g)).val.app (.op V)).hom s =
    ((FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f).val.app (.op V)).hom
      (((FrobeniusSplitting.CharacterLine.relativeFunctionsMap S g).val.app (.op V)).hom s)
  erw [FrobeniusSplitting.CharacterLine.relativeFunctionsMap_app S (f ≫ g) V,
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap_app S f V,
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap_app S g V]
  exact (congrArg (fun h => h s)
    (Scheme.Hom.appLE_comp_appLE f.left g.left
      (Z.hom ⁻¹ᵁ V) (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V)
      (FrobeniusSplitting.CharacterLine.overPreimage S g V)
          (FrobeniusSplitting.CharacterLine.overPreimage S f V))).symm

/-- Relative regular functions form the contravariant functor on the schemes over the base. -/
def relativeFunctions : (Over S)ᵒᵖ ⥤ S.Modules where
  obj X := FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X.unop
  map f := FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f.unop
  map_id X := FrobeniusSplitting.CharacterLine.relativeFunctionsMap_id S X.unop
  map_comp f g := by
    simpa only [unop_comp] using FrobeniusSplitting.CharacterLine.relativeFunctionsMap_comp S
        g.unop f.unop

end FrobeniusSplitting.CharacterLine
