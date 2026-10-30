import TauCeti.AlgebraicGeometry.Modules.Pullback

/-! # Structure sheaves under open restriction and pullback -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace GroupActions
noncomputable section
universe u

/-- Open restriction and pullback have the same structure-sheaf comparison. -/
theorem restrictPullback_unit {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctorIsoPullback j).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullbackObjUnitIso j).hom = (restrictUnitIso j).hom := by
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  apply ((restrictAdjunction j).homEquiv OY OX).injective
  have hn := (restrictAdjunction j).homEquiv_naturality_right
    ((restrictFunctorIsoPullback j).hom.app OY) (pullbackObjUnitIso j).hom
  have hu := congrArg (fun k => k ≫ (pushforward j).map (pullbackObjUnitIso j).hom)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app (restrictAdjunction j)
      (pullbackPushforwardAdjunction j) OY)
  have hr : (restrictAdjunction j).homEquiv OY OX (restrictUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
    change (restrictAdjunction j).unit.app OY ≫
      (pushforward j).map (restrictUnitIso j).hom = _
    ext U x
    change (j.appIso (j ⁻¹ᵁ U)).hom
      (Y.presheaf.map (homOfLE (j.image_preimage_le U)).op x) = j.app U x
    have hw : Y.presheaf.map (homOfLE (j.image_preimage_le U)).op ≫
        (j.appIso (j ⁻¹ᵁ U)).hom = j.app U :=
      (((j.appIso (j ⁻¹ᵁ U)).comp_inv_eq).mp (j.app_appIso_inv U)).symm
    exact ConcreteCategory.congr_hom hw x
  exact hn.trans (hu.trans
    ((pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom j).trans hr.symm))

end
end GroupActions
