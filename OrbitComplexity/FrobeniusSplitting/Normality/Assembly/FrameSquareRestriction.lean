import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition
import Batteries.Tactic.Lint

/-!
# Restriction of coframe squares

Restricting a coframe square along a morphism agrees with the square for
the composite morphism, through the pullback composition isomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
namespace FrobeniusSplitting.CharacterLine

open private pulled_coframe from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem square_prefix {A B C S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) (c : C ⟶ A)
    (htotal : (c ≫ k) ≫ b = (c ≫ a) ≫ q) (L : S.Modules) :
    (pullbackComp c a).inv.app ((Scheme.Modules.pullback q).obj L) ≫
        (Scheme.Modules.pullback c).map ((pullbackComp a q).hom.app L) ≫
        (Scheme.Modules.pullback c).map ((pullbackCongr h.symm).hom.app L) ≫
        (Scheme.Modules.pullback c).map ((pullbackComp k b).inv.app L) =
      (pullbackComp (c ≫ a) q).hom.app L ≫
        (pullbackCongr htotal.symm).hom.app L ≫
        (pullbackComp (c ≫ k) b).inv.app L ≫
        (pullbackComp c k).inv.app ((Scheme.Modules.pullback b).obj L) := by
  rw [pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app]
  simp only [pullbackCongr, eqToIso.hom, eqToHom_app,
    ← Category.assoc, eqToHom_trans]

set_option backward.isDefEq.respectTransparency.types false in
/-- A coframe square commutes with further pullback on its domain. -/
theorem squareFrameIso_domain_comp {A B C S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) (c : C ⟶ A)
    (htotal : (c ≫ k) ≫ b = (c ≫ a) ≫ q) (L : S.Modules)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B) :
    squareFrameIso q (c ≫ a) b (c ≫ k) htotal L E =
      ((pullbackComp c a).app ((Scheme.Modules.pullback q).obj L)).symm ≪≫
        (Scheme.Modules.pullback c).mapIso (squareFrameIso q a b k h L E) ≪≫
        pullbackObjUnitIso c := by
  apply Iso.ext
  simp only [squareFrameIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hp := square_prefix q a b k h c htotal L
  have hp' := congrArg (fun t => t ≫
    (Scheme.Modules.pullback c).map
      ((Scheme.Modules.pullback k).map E.hom ≫ (pullbackObjUnitIso k).hom) ≫
        (pullbackObjUnitIso c).hom) hp
  have ht := pulled_coframe c k ((Scheme.Modules.pullback b).obj L) E
  have ht' := congrArg (fun t => (pullbackComp (c ≫ a) q).hom.app L ≫
    (pullbackCongr htotal.symm).hom.app L ≫
      (pullbackComp (c ≫ k) b).inv.app L ≫ t) ht
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hp' ht'
  exact (hp'.trans ht').symm

end FrobeniusSplitting.CharacterLine
