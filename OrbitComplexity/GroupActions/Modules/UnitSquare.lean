import OrbitComplexity.GroupActions.Modules.UnitCoherence

/-! # Restriction of pullback along an invariant open square -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace GroupActions
noncomputable section
universe u

/-- An invariant open square identifies restriction of pullback with pullback of restriction. -/
def restrictPullbackIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ X) (a : Y ⟶ Y) (h : f ≫ j = j ≫ a) :
    pullback a ⋙ restrictFunctor j ≅ restrictFunctor j ⋙ pullback f :=
  Functor.isoWhiskerLeft (pullback a) (restrictFunctorIsoPullback j) ≪≫
    pullbackComp j a ≪≫ pullbackCongr h.symm ≪≫ (pullbackComp f j).symm ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback j).symm (pullback f)

/-- The open-square comparison preserves the canonical identifications of structure sheaves. -/
theorem restrictPullbackIso_unit {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ X) (a : Y ⟶ Y) (h : f ≫ j = j ≫ a) :
    (restrictPullbackIso j f a h).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pullback f).map (restrictUnitIso j).hom ≫ (pullbackObjUnitIso f).hom =
      (restrictFunctor j).map (pullbackObjUnitIso a).hom ≫ (restrictUnitIso j).hom := by
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let rj := (restrictUnitIso j).hom
  let uj := (pullbackObjUnitIso j).hom
  let uf := (pullbackObjUnitIso f).hom
  let ua := (pullbackObjUnitIso a).hom
  let ρ := restrictFunctorIsoPullback j
  have hj : ρ.inv.app OY ≫ rj = uj :=
    ((ρ.app OY).inv_comp_eq).mpr (restrictPullback_unit j).symm
  have ht : (pullback f).map (ρ.inv.app OY) ≫ (pullback f).map rj ≫ uf =
      (pullback f).map uj ≫ uf := by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun m => (pullback f).map m ≫ uf) hj
  have hc : (pullbackComp f j).inv.app OY ≫
        (pullback f).map (ρ.inv.app OY) ≫ (pullback f).map rj ≫ uf =
      (pullbackObjUnitIso (f ≫ j)).hom := by
    have hh := congrArg (fun m => (pullbackComp f j).inv.app OY ≫ m) ht
    have hh' : (pullbackComp f j).inv.app OY ≫
        (pullback f).map (ρ.inv.app OY) ≫ (pullback f).map rj ≫ uf =
        (pullbackComp f j).inv.app OY ≫ (pullback f).map uj ≫ uf := by
      simpa only [Category.assoc] using hh
    exact hh'.trans (pullbackObjUnitIso_comp f j)
  have he : (pullbackCongr h.symm).hom.app OY ≫
      (pullbackObjUnitIso (f ≫ j)).hom = (pullbackObjUnitIso (j ≫ a)).hom :=
    pullbackObjUnitIso_congr h.symm
  have ha : (pullbackComp j a).hom.app OY ≫ (pullbackObjUnitIso (j ≫ a)).hom =
      (pullback j).map ua ≫ uj :=
    ((pullbackComp j a).app OY).eq_inv_comp.mp (pullbackObjUnitIso_comp j a).symm
  change ρ.hom.app ((pullback a).obj OY) ≫ (pullbackComp j a).hom.app OY ≫
    (pullbackCongr h.symm).hom.app OY ≫ (pullbackComp f j).inv.app OY ≫
    (pullback f).map (ρ.inv.app OY) ≫ (pullback f).map rj ≫ uf =
      (restrictFunctor j).map ua ≫ rj
  rw [hc, he, ha]
  have hn := congrArg (fun m => m ≫ uj) (ρ.hom.naturality ua)
  have hu := congrArg (fun m => (restrictFunctor j).map ua ≫ m) (restrictPullback_unit j)
  have hn' : ρ.hom.app ((pullback a).obj OY) ≫ (pullback j).map ua ≫ uj =
      (restrictFunctor j).map ua ≫ ρ.hom.app OY ≫ uj := by
    exact (Category.assoc _ _ _).symm.trans
      (hn.symm.trans (Category.assoc _ _ _))
  exact hn'.trans hu

end
end GroupActions
