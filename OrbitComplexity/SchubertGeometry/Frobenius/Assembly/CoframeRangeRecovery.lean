import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeGenerators
import OrbitComplexity.FrobeniusSplitting.Cartier.GlobalCoframes
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
import Batteries.Tactic.Lint

/-!
# Recovering coframes from open ranges

A coframe on an open chart is determined by its coframe on the open image.
Thus the range restriction of a global coframe recovers its chart pullback.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem cancel_iso_prefix {C : Type*} [Category C] {A B D : C}
    (p : A ≅ B) (e f : B ≅ D) (h : p ≪≫ e = p ≪≫ f) : e = f := by
  apply Iso.ext
  apply (cancel_epi p.hom).mp
  exact congrArg Iso.hom h

/-- A coframe on an open chart is determined by the coframe on its image. -/
theorem coframeOverRange_injective {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) :
    Function.Injective (coframeOverRange j L) := by
  intro E F heq
  have he := coframeOnOpen_range j L E
  have hf := coframeOnOpen_range j L F
  have hc := congrArg (coframeOnOpen L j.opensRange) heq
  let p := (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j).symm).app L ≪≫
    ((pullbackComp j.isoOpensRange.inv j).app L).symm
  have hp :
      p ≪≫ (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso E ≪≫
          pullbackObjUnitIso j.isoOpensRange.inv =
      p ≪≫ (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso F ≪≫
          pullbackObjUnitIso j.isoOpensRange.inv := by
    simpa only [p, Iso.trans_assoc] using he.symm.trans (hc.trans hf)
  have hlocal := cancel_iso_prefix p _ _ hp
  let : IsIso j.isoOpensRange.inv.appTop := by
    change IsIso (Scheme.Γ.map j.isoOpensRange.inv.op)
    infer_instance
  have hi : Function.Injective j.isoOpensRange.inv.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso j.isoOpensRange.inv.appTop).injective
  exact FrobeniusSplitting.RetainedCharacter.frame_eq_of_pullback
    j.isoOpensRange.inv ((Scheme.Modules.pullback j).obj L) E F hi hlocal

/-- Agreement of a global coframe on an open range gives the chart pullback equality. -/
theorem coframe_global_chart_eq {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (F : L ≅ unitModule X)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A)
    (h : F.hom.over j.opensRange = (coframeOverRange j L E).hom) :
    (Scheme.Modules.pullback j).mapIso F ≪≫ pullbackObjUnitIso j = E := by
  apply coframeOverRange_injective j L
  have hr : (SheafOfModules.overFunctor X.ringCatSheaf j.opensRange).mapIso F =
      coframeOverRange j L E := Iso.ext h
  exact (coframeOverRange_global j L F).trans hr

end SchubertGeometry.ProjectiveCartier
