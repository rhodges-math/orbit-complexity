import OrbitComplexity.FrobeniusSplitting.Modules.RelativeFunctions

/-! # Relative functions over a composite -/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app M =
      𝟙 ((Scheme.Modules.pushforward f).obj M) := by
  apply Scheme.Modules.hom_ext
  intro V
  change M.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ V = f ⁻¹ᵁ V)).op = 𝟙 _
  exact CategoryTheory.Functor.map_id M.presheaf _

/-- For a composite, the relative function map is its original unit and composition map. -/
theorem relativeFunctionsMap_unit {S X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Over.mk (f ≫ q)) (Y := Over.mk
        q) (Over.homMk f rfl) =
      (Scheme.Modules.pushforward q).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f q).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  let a := (Scheme.Modules.pushforward q).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  let b := (Scheme.Modules.pushforwardComp f q).hom.app (SheafOfModules.unit X.ringCatSheaf)
  let c := (Scheme.Modules.pushforwardCongr (rfl : f ≫ q = f ≫ q)).hom.app
    (SheafOfModules.unit X.ringCatSheaf)
  change a ≫ b ≫ c = a ≫ b
  exact (Category.assoc a b c).symm.trans
    ((congrArg (fun t => (a ≫ b) ≫ t)
      (FrobeniusSplitting.CharacterLine.pushforwardCongr_refl (f ≫ q) (SheafOfModules.unit
          X.ringCatSheaf))).trans
        (Category.comp_id (a ≫ b)))

end FrobeniusSplitting.CharacterLine
