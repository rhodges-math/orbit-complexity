import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeGenerators
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenCoframes
import OrbitComplexity.FrobeniusSplitting.Cartier.OverCoframeReflection
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction
import Batteries.Tactic.Lint

/-!
# Generator sections of open coframes

The coframe on the open range of an immersion has the generator obtained
by transporting the inverse chart coframe along that immersion.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem restrict_unit_adjunct {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] :
    (restrictAdjunction j).homEquiv (unitModule X) (unitModule A)
      (restrictUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
  ext U r
  change (j.appIso (j ⁻¹ᵁ U)).hom
      (X.presheaf.map (homOfLE (j.image_preimage_le U)).op r) = j.app U r
  have h := j.app_appIso_inv U
  have h' := congrArg (fun t => t ≫ (j.appIso (j ⁻¹ᵁ U)).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
  exact (congrArg (fun t => t.hom r) h').symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem restrict_unit_comparison {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] :
    (restrictFunctorIsoPullback j).hom.app (unitModule X) ≫
      (pullbackObjUnitIso j).hom = (restrictUnitIso j).hom := by
  apply ((restrictAdjunction j).homEquiv (unitModule X) (unitModule A)).injective
  have ha : (restrictAdjunction j).homEquiv (unitModule X)
      ((Scheme.Modules.pullback j).obj (unitModule X))
      ((restrictFunctorIsoPullback j).hom.app (unitModule X)) =
      (pullbackPushforwardAdjunction j).unit.app (unitModule X) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (restrictAdjunction j) (pullbackPushforwardAdjunction j) (unitModule X)
  rw [Adjunction.homEquiv_naturality_right, ha]
  rw [← Adjunction.homEquiv_unit]
  exact (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom j).trans
    (restrict_unit_adjunct j).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem open_unit_comparison {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] :
    (openUnitComparison j).hom =
      (overFunctorEquiv j.opensRange).hom.app (unitModule X) ≫
        (restrictUnitIso j.opensRange.ι).hom := by
  have hu : (pullbackComp j.isoOpensRange.inv j).inv.app (unitModule X) ≫
      (Scheme.Modules.pullback j.isoOpensRange.inv).map (pullbackObjUnitIso j).hom ≫
        (pullbackObjUnitIso j.isoOpensRange.inv).hom =
        (pullbackObjUnitIso (j.isoOpensRange.inv ≫ j)).hom :=
    pullbackObjUnitIso_comp j.isoOpensRange.inv j
  have hc : (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j)).inv.app
        (unitModule X) ≫ (pullbackObjUnitIso (j.isoOpensRange.inv ≫ j)).hom =
      (pullbackObjUnitIso j.opensRange.ι).hom := by
    simpa only [pullbackCongr, eqToIso.inv, eqToIso.hom, eqToHom_app] using
      pullbackObjUnitIso_congr (Scheme.Hom.isoOpensRange_inv_comp j).symm
  have hh :
      (overFunctorEquiv j.opensRange).hom.app (unitModule X) ≫
        (restrictFunctorIsoPullback j.opensRange.ι).hom.app (unitModule X) ≫
        (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j)).inv.app (unitModule X) ≫
        (pullbackComp j.isoOpensRange.inv j).inv.app (unitModule X) ≫
        (Scheme.Modules.pullback j.isoOpensRange.inv).map (pullbackObjUnitIso j).hom ≫
        (pullbackObjUnitIso j.isoOpensRange.inv).hom =
      (overFunctorEquiv j.opensRange).hom.app (unitModule X) ≫
        (restrictUnitIso j.opensRange.ι).hom := by
    rw [hu, hc, restrict_unit_comparison]
  simpa only [openUnitComparison, openModuleComparison, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc] using hh

private theorem cancel_iso_frame {C : Type*} [Category C]
    {A0 A1 B0 P0 Q0 U0 U1 U2 : C}
    (a : A0 ≅ A1) (b : B0 ≅ A0) (p : A1 ≅ P0)
    (q : P0 ≅ Q0) (v : Q0 ≅ U2) (bu : U0 ≅ U1) (ru : U1 ≅ U2)
    (ou : U0 ≅ U2) (f : B0 ≅ U0)
    (hf : f.hom = ((b ≪≫ a ≪≫ p) ≪≫ q ≪≫ v ≪≫ ou.symm).hom)
    (hu : ou.hom = (bu ≪≫ ru).hom) :
    a.symm ≪≫ b.symm ≪≫ f ≪≫ bu ≪≫ ru = p ≪≫ q ≪≫ v := by
  have hu' : ou = bu ≪≫ ru := Iso.ext hu
  have hf' : f = (b ≪≫ a ≪≫ p) ≪≫ q ≪≫ v ≪≫ ou.symm := Iso.ext hf
  subst f
  subst ou
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- Passing from an open-range coframe back to its scheme restriction gives
the coframe pulled along the inverse open-range isomorphism. -/
theorem coframeOnOpen_range {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    coframeOnOpen L j.opensRange (coframeOverRange j L E) =
      (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j).symm).app L ≪≫
        ((pullbackComp j.isoOpensRange.inv j).app L).symm ≪≫
          (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso E ≪≫
            pullbackObjUnitIso j.isoOpensRange.inv := by
  let a := (restrictFunctorIsoPullback j.opensRange.ι).app L
  let b := (overFunctorEquiv j.opensRange).app L
  let p := (pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j).symm).app L ≪≫
    ((pullbackComp j.isoOpensRange.inv j).app L).symm
  let q := (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso E
  let v := pullbackObjUnitIso j.isoOpensRange.inv
  let bu := (overFunctorEquiv j.opensRange).app (unitModule X)
  let ru := restrictUnitIso j.opensRange.ι
  let ou := openUnitComparison j
  let f := (overEquiv j.opensRange).functor.mapIso (coframeOverRange j L E)
  have hmodule : openModuleComparison j L = b ≪≫ a ≪≫ p := by
    apply Iso.ext
    simp only [openModuleComparison, a, b, p, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, pullbackCongr, eqToIso.inv, eqToIso.hom, eqToHom_app]
  have hf : f.hom = ((b ≪≫ a ≪≫ p) ≪≫ q ≪≫ v ≪≫ ou.symm).hom := by
    simpa only [f, q, v, ou, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom, Category.assoc, ← hmodule] using
      coframeOverRange_hom j L E
  have hu : ou.hom = (bu ≪≫ ru).hom := open_unit_comparison j
  exact cancel_iso_frame a b p q v bu ru ou f hf hu

end SchubertGeometry.ProjectiveCartier
