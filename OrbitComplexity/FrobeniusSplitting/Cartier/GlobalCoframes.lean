import OrbitComplexity.FrobeniusSplitting.Cartier.OpenCoframes
import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeGluing
import Batteries.Tactic.Lint

/-!
# Global coframes and open chart pullbacks

A global coframe induces its restriction on every open chart image.
Equality of global coframes can be checked after pullback to an open cover.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.OperatorSheaf

open private hom_ext_on_cover from
  OrbitComplexity.FrobeniusSplitting.Cartier.CoframeGluing

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def rangeModuleComparison {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] :
    SheafOfModules.overFunctor X.ringCatSheaf j.opensRange ⋙
      (overEquiv j.opensRange).functor ≅
      Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback j.isoOpensRange.inv :=
  overFunctorEquiv j.opensRange ≪≫ restrictFunctorIsoPullback j.opensRange.ι ≪≫
    (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j)).symm ≪≫
      (pullbackComp j.isoOpensRange.inv j).symm

private theorem natural_frame {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (a : F ≅ G) {M O : C} {T : D}
    (v : G.obj O ≅ T) (u : F.obj O ≅ T) (e : M ≅ O)
    (hu : u = a.app O ≪≫ v) :
    a.app M ≪≫ G.mapIso e ≪≫ v ≪≫ u.symm = F.mapIso e := by
  subst u
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    CategoryTheory.Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have h := a.hom.naturality_assoc e.hom (a.inv.app O)
  simp only [Iso.hom_inv_id_app, Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The coframe on the range of a pulled global coframe is its restriction. -/
theorem coframeOverRange_global {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (E : L ≅ unitModule X) :
    coframeOverRange j L
        ((Scheme.Modules.pullback j).mapIso E ≪≫ pullbackObjUnitIso j) =
      (SheafOfModules.overFunctor X.ringCatSheaf j.opensRange).mapIso E := by
  apply Iso.ext
  apply (overEquiv j.opensRange).functor.map_injective
  let F := SheafOfModules.overFunctor X.ringCatSheaf j.opensRange ⋙
    (overEquiv j.opensRange).functor
  let G := Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback j.isoOpensRange.inv
  let a : F ≅ G := rangeModuleComparison j
  let v : G.obj (unitModule X) ≅ unitModule j.opensRange.toScheme :=
    (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso
    (pullbackObjUnitIso j) ≪≫ pullbackObjUnitIso j.isoOpensRange.inv
  let u : F.obj (unitModule X) ≅ unitModule j.opensRange.toScheme := openUnitComparison j
  have hu : u = a.app (unitModule X) ≪≫ v := rfl
  have hn := congrArg Iso.hom (natural_frame F G a v u E hu)
  have happ : (rangeModuleComparison j).hom.app L = (openModuleComparison j L).hom := rfl
  have hr := coframeOverRange_hom j L
    ((Scheme.Modules.pullback j).mapIso E ≪≫ pullbackObjUnitIso j)
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc] at hr
  apply hr.trans
  simpa only [F, G, a, v, u, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.comp_map, Category.assoc, happ] using hn

/-- Equality of global coframes can be tested on all chart pullbacks of an open cover. -/
theorem coframe_eq_of_chart_pullback {X : Scheme.{u}} (U : Scheme.OpenCover.{u} X)
    (L : X.Modules) (E F : L ≅ unitModule X)
    (h : ∀ i, (Scheme.Modules.pullback (U.f i)).mapIso E ≪≫
        pullbackObjUnitIso (U.f i) =
      (Scheme.Modules.pullback (U.f i)).mapIso F ≪≫
        pullbackObjUnitIso (U.f i)) : E = F := by
  apply Iso.ext
  apply hom_ext_on_cover (fun i => (U.f i).opensRange) U.iSup_opensRange L
    (unitModule X) E.hom F.hom
  intro i
  have he := congrArg (coframeOverRange (U.f i) L) (h i)
  rw [coframeOverRange_global, coframeOverRange_global] at he
  exact congrArg Iso.hom he

end FrobeniusSplitting.OperatorSheaf
