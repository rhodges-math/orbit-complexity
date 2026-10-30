import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeGenerators
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OverFunctorComponents
import OrbitComplexity.FrobeniusSplitting.Cartier.OverModuleComponents
import Batteries.Tactic.Lint

/-!
# Sections of coframes on open ranges

The generator of a coframe on an open subset agrees with the section
obtained from its associated coframe on the open subscheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private imageSectionAt from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme restriction of an open coframe has the same generator section. -/
theorem openFrameSection_onOpen {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U) :
    openFrameSection U.ι L (coframeOnOpen L U E) =
      (L.val.map (eqToHom U.opensRange_ι).op).hom (coframeGenerator L U E) := by
  let g : unitModule U.toScheme ⟶ (restrictFunctor U.ι).obj L :=
    (restrictUnitIso U.ι).inv ≫ (overFunctorEquiv U).inv.app (unitModule X) ≫
      (overEquiv U).functor.map E.inv ≫ (overFunctorEquiv U).hom.app L
  have hh : (coframeOnOpen L U E).inv ≫
      (restrictFunctorIsoPullback U.ι).inv.app L = g := by
    simp only [coframeOnOpen, Iso.trans_inv, Iso.symm_inv,
      CategoryTheory.Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id, g]
  have heval : ((coframeOnOpen L U E).inv ≫
      (restrictFunctorIsoPullback U.ι).inv.app L).app ⊤ (1 : Γ(U.toScheme, ⊤)) =
      g.app ⊤ (1 : Γ(U.toScheme, ⊤)) :=
    congrArg (fun f => f.app ⊤ (1 : Γ(U.toScheme, ⊤))) hh
  unfold openFrameSection imageSectionAt
  change (L.val.map (eqToHom U.ι.image_top_eq_opensRange.symm).op).hom
      ((L.restrictAppIso U.ι ⊤).hom
        (((coframeOnOpen L U E).inv ≫
          (restrictFunctorIsoPullback U.ι).inv.app L).app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  rw [heval]
  have hval : (L.restrictAppIso U.ι ⊤).hom (g.app ⊤ (1 : Γ(U.toScheme, ⊤))) =
      (L.val.map (eqToHom U.ι_image_top).op).hom (coframeGenerator L U E) := by
    change ((overFunctorEquiv U).hom.app L).app ⊤
        (((overEquiv U).functor.map E.inv).app ⊤
          (((overFunctorEquiv U).inv.app (unitModule X)).app ⊤
            ((restrictUnitIso U.ι).inv.app ⊤ (1 : Γ(U.toScheme, ⊤))))) = _
    rw [overFunctorEquiv_hom_apply, overFunctorEquiv_inv_apply, restrictUnitIso_inv_one]
    let W := U.overEquivalence.inverse.obj ⊤
    change (((U.sheafOfModulesEquivOver X.ringCatSheaf).functor.map E.inv).val.app
        (op ⊤)).hom (1 : Γ(X, W.left)) = _
    rw [overModuleEquiv_map_apply]
    let hV : W ⟶ Over.mk (𝟙 U) := Over.homMk W.hom (by simp)
    exact (((L.over U).unitHomEquiv E.inv).property hV.op).symm

  rw [hval]
  rw [← L.val.map_comp_apply]
  rfl

end SchubertGeometry.ProjectiveCartier
