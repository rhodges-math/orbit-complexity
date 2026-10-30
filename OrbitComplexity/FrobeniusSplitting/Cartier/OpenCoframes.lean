import TauCeti.AlgebraicGeometry.Modules.Pullback
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Batteries.Tactic.Lint

/-!
# Coframes on the range of an open immersion

A coframe on an open chart determines a coframe of the same module on its
open range. The comparison retains both directions of the isomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The module on an open range compares with the chart module pulled to that range. -/
def openModuleComparison {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) :
    (overEquiv j.opensRange).functor.obj (L.over j.opensRange) ≅
      (Scheme.Modules.pullback j.isoOpensRange.inv).obj
        ((Scheme.Modules.pullback j).obj L) :=
  (overFunctorEquiv j.opensRange).app L ≪≫
    (restrictFunctorIsoPullback j.opensRange.ι).app L ≪≫
      (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j)).symm.app L ≪≫
        (pullbackComp j.isoOpensRange.inv j).symm.app L

/-- The structure module on an open range has its chart-induced unit comparison. -/
def openUnitComparison {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] :
    (overEquiv j.opensRange).functor.obj ((unitModule X).over j.opensRange) ≅
      unitModule (j.opensRange : Scheme.{u}) :=
  openModuleComparison j (unitModule X) ≪≫
    (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso (pullbackObjUnitIso j) ≪≫
      pullbackObjUnitIso j.isoOpensRange.inv

private def rangeCoframe {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    (overEquiv j.opensRange).functor.obj (L.over j.opensRange) ≅
      (overEquiv j.opensRange).functor.obj ((unitModule X).over j.opensRange) :=
  openModuleComparison j L ≪≫
    (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso E ≪≫
      pullbackObjUnitIso j.isoOpensRange.inv ≪≫ (openUnitComparison j).symm

/-- A chart coframe gives a coframe on its open range without changing the module. -/
def coframeOverRange {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    L.over j.opensRange ≅ (unitModule X).over j.opensRange :=
  (overEquiv j.opensRange).functor.preimageIso (rangeCoframe j L E)

/-- The coframe on the range retains the chart's forward map through the module comparisons. -/
theorem coframeOverRange_hom {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    (overEquiv j.opensRange).functor.map (coframeOverRange j L E).hom =
      (openModuleComparison j L).hom ≫
        (Scheme.Modules.pullback j.isoOpensRange.inv).map E.hom ≫
          (pullbackObjUnitIso j.isoOpensRange.inv).hom ≫ (openUnitComparison j).inv := by
  change (overEquiv j.opensRange).functor.map
    ((overEquiv j.opensRange).functor.preimage (rangeCoframe j L E).hom) = _
  exact CategoryTheory.Functor.map_preimage _ _

/-- The coframe on the range retains the chart's inverse map through the module comparisons. -/
theorem coframeOverRange_inv {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (L : X.Modules) (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    (overEquiv j.opensRange).functor.map (coframeOverRange j L E).inv =
      (openUnitComparison j).hom ≫ (pullbackObjUnitIso j.isoOpensRange.inv).inv ≫
        (Scheme.Modules.pullback j.isoOpensRange.inv).map E.inv ≫
          (openModuleComparison j L).inv := by
  change (overEquiv j.opensRange).functor.map
    ((overEquiv j.opensRange).functor.preimage (rangeCoframe j L E).inv) = _
  exact CategoryTheory.Functor.map_preimage _ _

end FrobeniusSplitting.OperatorSheaf
