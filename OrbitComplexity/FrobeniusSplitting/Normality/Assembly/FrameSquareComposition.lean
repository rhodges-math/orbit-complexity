import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import Batteries.Tactic.Lint

/-!
# Composition of coframe squares

The coframe comparison for two successive scalar squares agrees with the
comparison for their composite, retaining the pullback composition isomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.CharacterLine

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem pulled_coframe {A B C : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C)
    (L : C.Modules) (E : L ≅ unitModule C) :
    (pullbackComp u v).inv.app L ≫
        (Scheme.Modules.pullback u).map
          ((Scheme.Modules.pullback v).map E.hom ≫ (pullbackObjUnitIso v).hom) ≫
        (pullbackObjUnitIso u).hom =
      (Scheme.Modules.pullback (u ≫ v)).map E.hom ≫ (pullbackObjUnitIso (u ≫ v)).hom := by
  have hn : (pullbackComp u v).inv.app L ≫
      (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map E.hom) =
      (Scheme.Modules.pullback (u ≫ v)).map E.hom ≫
        (pullbackComp u v).inv.app (unitModule C) :=
    ((pullbackComp u v).inv.naturality E.hom).symm
  rw [CategoryTheory.Functor.map_comp]
  calc
    (pullbackComp u v).inv.app L ≫
        ((Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map E.hom) ≫
          (Scheme.Modules.pullback u).map (pullbackObjUnitIso v).hom) ≫
        (pullbackObjUnitIso u).hom =
      ((pullbackComp u v).inv.app L ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map E.hom)) ≫
          ((Scheme.Modules.pullback u).map (pullbackObjUnitIso v).hom ≫
            (pullbackObjUnitIso u).hom) := by simp only [Category.assoc]
    _ = ((Scheme.Modules.pullback (u ≫ v)).map E.hom ≫
        (pullbackComp u v).inv.app (unitModule C)) ≫
          ((Scheme.Modules.pullback u).map (pullbackObjUnitIso v).hom ≫
            (pullbackObjUnitIso u).hom) := by rw [hn]
    _ = (Scheme.Modules.pullback (u ≫ v)).map E.hom ≫
        ((pullbackComp u v).inv.app (unitModule C) ≫
          (Scheme.Modules.pullback u).map (pullbackObjUnitIso v).hom ≫
            (pullbackObjUnitIso u).hom) := Category.assoc _ _ _
    _ = (Scheme.Modules.pullback (u ≫ v)).map E.hom ≫
        (pullbackObjUnitIso (u ≫ v)).hom :=
      congrArg (fun t => (Scheme.Modules.pullback (u ≫ v)).map E.hom ≫ t)
        (pullbackObjUnitIso_comp u v)

private theorem chart_prefix {A B C S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (c : C ⟶ S) (u : A ⟶ B) (v : B ⟶ C)
    (h : u ≫ (v ≫ c) = a ≫ q) (h' : (u ≫ v) ≫ c = a ≫ q)
    (L : S.Modules) :
    (pullbackComp a q).hom.app L ≫ (pullbackCongr h.symm).hom.app L ≫
        (pullbackComp u (v ≫ c)).inv.app L ≫
          (Scheme.Modules.pullback u).map ((pullbackComp v c).inv.app L) =
      (pullbackComp a q).hom.app L ≫ (pullbackCongr h'.symm).hom.app L ≫
        (pullbackComp (u ≫ v) c).inv.app L ≫
          (pullbackComp u v).inv.app ((Scheme.Modules.pullback c).obj L) := by
  have ht : (pullbackCongr h.symm).hom.app L ≫
        eqToHom (show (Scheme.Modules.pullback (u ≫ (v ≫ c))).obj L =
          (Scheme.Modules.pullback ((u ≫ v) ≫ c)).obj L by rw [Category.assoc]) =
      (pullbackCongr h'.symm).hom.app L := by
    simp only [pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans]
  rw [pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app]
  simpa only [Category.assoc] using
    congrArg (fun t => (pullbackComp a q).hom.app L ≫ t ≫
      (pullbackComp (u ≫ v) c).inv.app L ≫
        (pullbackComp u v).inv.app ((Scheme.Modules.pullback c).obj L)) ht

set_option backward.isDefEq.respectTransparency.types false in
/-- Composing chart maps preserves the coframe comparison on the same original line. -/
theorem squareFrameIso_chart_comp {A B C S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (c : C ⟶ S) (u : A ⟶ B) (v : B ⟶ C)
    (h : u ≫ (v ≫ c) = a ≫ q) (h' : (u ≫ v) ≫ c = a ≫ q)
    (L : S.Modules)
    (E : (Scheme.Modules.pullback c).obj L ≅ unitModule C) :
    squareFrameIso q a (v ≫ c) u h L
        (((pullbackComp v c).app L).symm ≪≫
          (Scheme.Modules.pullback v).mapIso E ≪≫ pullbackObjUnitIso v) =
      squareFrameIso q a c (u ≫ v) h' L E := by
  apply Iso.ext
  simp only [squareFrameIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hp := chart_prefix q a c u v h h' L
  have hp' := congrArg (fun t => t ≫
      (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map E.hom) ≫
        (Scheme.Modules.pullback u).map (pullbackObjUnitIso v).hom ≫
          (pullbackObjUnitIso u).hom) hp
  have ht := pulled_coframe u v ((Scheme.Modules.pullback c).obj L) E
  rw [CategoryTheory.Functor.map_comp] at ht
  have ht' := congrArg (fun t => (pullbackComp a q).hom.app L ≫
    (pullbackCongr h'.symm).hom.app L ≫
      (pullbackComp (u ≫ v) c).inv.app L ≫ t) ht
  simp only [Category.assoc] at hp' ht'
  exact hp'.trans ht'

end FrobeniusSplitting.CharacterLine
