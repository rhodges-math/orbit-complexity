import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Composition of coframe comparison squares

Two composable chart squares carry the coframe through the same pullback
comparison as their composite. The prescribed total maps are retained in
the result, together with the comparison of the original line module.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

open private pulled_coframe from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition

namespace FrobeniusSplitting.CharacterLine

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem stack_prefix {A B C S T V : Scheme.{u}}
    (q : T ⟶ S) (r : V ⟶ T) (a : A ⟶ V) (b : B ⟶ T) (c : C ⟶ S)
    (u : A ⟶ B) (v : B ⟶ C)
    (h₁ : u ≫ b = a ≫ r) (h₀ : v ≫ c = b ≫ q)
    (h : (u ≫ v) ≫ c = a ≫ (r ≫ q)) (L : S.Modules) :
    (pullbackComp a r).hom.app ((Scheme.Modules.pullback q).obj L) ≫
        (pullbackCongr h₁.symm).hom.app ((Scheme.Modules.pullback q).obj L) ≫
        (pullbackComp u b).inv.app ((Scheme.Modules.pullback q).obj L) ≫
        (Scheme.Modules.pullback u).map ((pullbackComp b q).hom.app L) ≫
        (Scheme.Modules.pullback u).map ((pullbackCongr h₀.symm).hom.app L) ≫
        (Scheme.Modules.pullback u).map ((pullbackComp v c).inv.app L) =
      (Scheme.Modules.pullback a).map ((pullbackComp r q).hom.app L) ≫
        (pullbackComp a (r ≫ q)).hom.app L ≫ (pullbackCongr h.symm).hom.app L ≫
        (pullbackComp (u ≫ v) c).inv.app L ≫
        (pullbackComp u v).inv.app ((Scheme.Modules.pullback c).obj L) := by
  rw [pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app]
  rw [pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc]
  simp only [pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]

private theorem paste_frame_maps {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {N₀ N₁ N₂ N₃ U : C} {P₀ P₁ P₂ R₀ R₁ R₂ R₃ Q : D}
    (x₀ : P₀ ⟶ P₁) (x₁ : P₁ ⟶ P₂) (x₂ : P₂ ⟶ F.obj N₀)
    (y₀ : N₀ ⟶ N₁) (y₁ : N₁ ⟶ N₂) (y₂ : N₂ ⟶ N₃)
    (t : N₃ ⟶ U) (e : F.obj U ⟶ Q)
    (d₀ : P₀ ⟶ R₀) (d₁ : R₀ ⟶ R₁) (d₂ : R₁ ⟶ R₂) (d₃ : R₂ ⟶ R₃)
    (i : R₃ ⟶ F.obj N₃) (s : R₃ ⟶ Q)
    (hp : x₀ ≫ x₁ ≫ x₂ ≫ F.map y₀ ≫ F.map y₁ ≫ F.map y₂ =
      d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ i)
    (hu : i ≫ F.map t ≫ e = s) :
    x₀ ≫ x₁ ≫ x₂ ≫ F.map (y₀ ≫ y₁ ≫ y₂ ≫ t) ≫ e =
      d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ s := by
  calc
    _ = (x₀ ≫ x₁ ≫ x₂ ≫ F.map y₀ ≫ F.map y₁ ≫ F.map y₂) ≫
        (F.map t ≫ e) := by simp only [Functor.map_comp, Category.assoc]
    _ = (d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ i) ≫ (F.map t ≫ e) :=
      congrArg (fun k => k ≫ (F.map t ≫ e)) hp
    _ = _ := by simp only [Category.assoc]; rw [hu]

private theorem stack_coframe {A B C S T V : Scheme.{u}}
    (q : T ⟶ S) (r : V ⟶ T) (a : A ⟶ V) (b : B ⟶ T) (c : C ⟶ S)
    (u : A ⟶ B) (v : B ⟶ C)
    (h₁ : u ≫ b = a ≫ r) (h₀ : v ≫ c = b ≫ q)
    (h : (u ≫ v) ≫ c = a ≫ (r ≫ q)) (L : S.Modules)
    (E : (Scheme.Modules.pullback c).obj L ≅ unitModule C) :
    squareFrameIso r a b u h₁ ((Scheme.Modules.pullback q).obj L)
        (squareFrameIso q b c v h₀ L E) =
      (Scheme.Modules.pullback a).mapIso ((pullbackComp r q).app L) ≪≫
        squareFrameIso (r ≫ q) a c (u ≫ v) h L E := by
  apply Iso.ext
  exact paste_frame_maps (Scheme.Modules.pullback u)
    ((pullbackComp a r).hom.app ((Scheme.Modules.pullback q).obj L))
    ((pullbackCongr h₁.symm).hom.app ((Scheme.Modules.pullback q).obj L))
    ((pullbackComp u b).inv.app ((Scheme.Modules.pullback q).obj L))
    ((pullbackComp b q).hom.app L) ((pullbackCongr h₀.symm).hom.app L)
    ((pullbackComp v c).inv.app L)
    ((Scheme.Modules.pullback v).map E.hom ≫ (pullbackObjUnitIso v).hom)
    (pullbackObjUnitIso u).hom
    ((Scheme.Modules.pullback a).map ((pullbackComp r q).hom.app L))
    ((pullbackComp a (r ≫ q)).hom.app L) ((pullbackCongr h.symm).hom.app L)
    ((pullbackComp (u ≫ v) c).inv.app L)
    ((pullbackComp u v).inv.app ((Scheme.Modules.pullback c).obj L))
    ((Scheme.Modules.pullback (u ≫ v)).map E.hom ≫ (pullbackObjUnitIso (u ≫ v)).hom)
    (stack_prefix q r a b c u v h₁ h₀ h L)
    (pulled_coframe u v ((Scheme.Modules.pullback c).obj L) E)

/-- Two comparison squares compose through the prescribed total maps and
preserve the whole comparison of the original line module. -/
theorem squareFrameIso_stack_eq {A B C S T V : Scheme.{u}}
    (q : T ⟶ S) (r : V ⟶ T) (a : A ⟶ V) (b : B ⟶ T) (c : C ⟶ S)
    (u : A ⟶ B) (v : B ⟶ C) (q₀ : V ⟶ S) (k₀ : A ⟶ C)
    (hbase : r ≫ q = q₀) (hchart : u ≫ v = k₀)
    (h₁ : u ≫ b = a ≫ r) (h₀ : v ≫ c = b ≫ q)
    (htotal : k₀ ≫ c = a ≫ q₀) (L : S.Modules)
    (E : (Scheme.Modules.pullback c).obj L ≅ unitModule C) :
    squareFrameIso r a b u h₁ ((Scheme.Modules.pullback q).obj L)
        (squareFrameIso q b c v h₀ L E) =
      (Scheme.Modules.pullback a).mapIso
          ((pullbackComp r q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫
        squareFrameIso q₀ a c k₀ htotal L E := by
  subst q₀
  subst k₀
  have hframe : (pullbackComp r q).app L ≪≫
      (pullbackCongr (rfl : r ≫ q = r ≫ q)).app L = (pullbackComp r q).app L := by
    change (pullbackComp r q).app L ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  have hmap := congrArg (fun F => (Scheme.Modules.pullback a).mapIso F) hframe
  exact (stack_coframe q r a b c u v h₁ h₀ htotal L E).trans
    (congrArg (fun F => F ≪≫ squareFrameIso (r ≫ q) a c (u ≫ v) htotal L E) hmap.symm)

end FrobeniusSplitting.CharacterLine
