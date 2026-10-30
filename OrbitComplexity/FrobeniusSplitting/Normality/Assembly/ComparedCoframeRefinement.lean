import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareStacking
import Batteries.Tactic.Lint

/-! # Refinement of a compared coframe

A line isomorphism and a chart triangle determine a coframe on the whole
chart. Restricting that coframe agrees with using the same isomorphism and
triangle on a finer chart.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem append_equality {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (d : A ⟶ E) (e : E ⟶ D) (c : D ⟶ F)
    (h : a ≫ b = d ≫ e) : a ≫ b ≫ c = (d ≫ e) ≫ c :=
  (Category.assoc a b c).symm.trans (congrArg (fun t => t ≫ c) h)

private theorem refinement_prefix {X P Y Z : Scheme.{u}}
    (k : X ⟶ P) (f : P ⟶ Y) (r : Y ⟶ Z)
    (h : (k ≫ f) ≫ r = k ≫ (f ≫ r))
    (L : Y.Modules) (LK : Z.Modules)
    (EL : L ≅ (Scheme.Modules.pullback r).obj LK) :
    (pullbackComp k f).inv.app L ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback f).map EL.hom) ≫
        (Scheme.Modules.pullback k).map ((pullbackComp f r).hom.app LK) =
      (Scheme.Modules.pullback (k ≫ f)).map EL.hom ≫
        (pullbackComp (k ≫ f) r).hom.app LK ≫
        (pullbackCongr h).hom.app LK ≫ (pullbackComp k (f ≫ r)).inv.app LK := by
  calc
    _ = ((Scheme.Modules.pullback (k ≫ f)).map EL.hom ≫
        (pullbackComp k f).inv.app ((Scheme.Modules.pullback r).obj LK)) ≫
        (Scheme.Modules.pullback k).map ((pullbackComp f r).hom.app LK) := by
      exact append_equality _ _ _ _ _ ((pullbackComp k f).inv.naturality EL.hom).symm
    _ = _ := by
      rw [Category.assoc,
        pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app]
      rfl

private theorem paste_refinement {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {N₀ N₁ N₂ U : C} {P Q₀ Q₁ Q₂ W : D}
    (p : P ⟶ F.obj N₀) (x : N₀ ⟶ N₁) (y : N₁ ⟶ N₂)
    (e : N₂ ⟶ U) (w : F.obj U ⟶ W)
    (q₀ : P ⟶ Q₀) (q₁ : Q₀ ⟶ Q₁) (q₂ : Q₁ ⟶ Q₂)
    (q₃ : Q₂ ⟶ F.obj N₂)
    (hp : p ≫ F.map x ≫ F.map y = q₀ ≫ q₁ ≫ q₂ ≫ q₃) :
    q₀ ≫ q₁ ≫ q₂ ≫ q₃ ≫ F.map e ≫ w =
      p ≫ F.map (x ≫ y ≫ e) ≫ w := by
  calc
    _ = (q₀ ≫ q₁ ≫ q₂ ≫ q₃) ≫ (F.map e ≫ w) := by
      simp only [Category.assoc]
    _ = (p ≫ F.map x ≫ F.map y) ≫ (F.map e ≫ w) :=
      congrArg (fun t => t ≫ (F.map e ≫ w)) hp.symm
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

private theorem primitive_refinement {X P Y Z : Scheme.{u}}
    (k : X ⟶ P) (f : P ⟶ Y) (r : Y ⟶ Z)
    (h : (k ≫ f) ≫ r = k ≫ (f ≫ r))
    (L : Y.Modules) (LK : Z.Modules)
    (EL : L ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback (f ≫ r)).obj LK ≅ unitModule P) :
    (Scheme.Modules.pullback (k ≫ f)).mapIso EL ≪≫
        (pullbackComp (k ≫ f) r).app LK ≪≫ (pullbackCongr h).app LK ≪≫
        ((pullbackComp k (f ≫ r)).app LK).symm ≪≫
        (Scheme.Modules.pullback k).mapIso E ≪≫ pullbackObjUnitIso k =
      ((pullbackComp k f).app L).symm ≪≫
        (Scheme.Modules.pullback k).mapIso
          ((Scheme.Modules.pullback f).mapIso EL ≪≫ (pullbackComp f r).app LK ≪≫ E) ≪≫
        pullbackObjUnitIso k := by
  apply Iso.ext
  exact paste_refinement (Scheme.Modules.pullback k)
    ((pullbackComp k f).inv.app L)
    ((Scheme.Modules.pullback f).map EL.hom) ((pullbackComp f r).hom.app LK)
    E.hom (pullbackObjUnitIso k).hom
    ((Scheme.Modules.pullback (k ≫ f)).map EL.hom)
    ((pullbackComp (k ≫ f) r).hom.app LK) ((pullbackCongr h).hom.app LK)
    ((pullbackComp k (f ≫ r)).inv.app LK)
    (refinement_prefix k f r h L LK EL)

private theorem erase_refinement {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {N₀ N₁ N₂ U : C} {P W : D}
    (p : P ≅ F.obj N₀) (x : N₀ ≅ N₁) (y : N₁ ≅ N₂)
    (E : N₂ ≅ U) (w : F.obj U ≅ W) :
    Iso.refl P ≪≫ p ≪≫ F.mapIso (x ≪≫ y ≪≫ Iso.refl N₂ ≪≫ E) ≪≫ w =
      p ≪≫ F.mapIso (x ≪≫ y ≪≫ E) ≪≫ w := by
  simp only [Iso.refl_trans]

/-- A compared coframe on a refinement is the restriction of the coframe
constructed from the same line isomorphism on the whole chart. -/
theorem comparedCoframe_refine {X P Y Z : Scheme.{u}}
    (r : Y ⟶ Z) (j : X ⟶ Y) (f : P ⟶ Y) (k : X ⟶ P) (g : P ⟶ Z)
    (hj : j = k ≫ f) (hf : f ≫ r = g) (h : j ≫ r = k ≫ g)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : L ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback g).obj LK ≅ unitModule P) :
    (Scheme.Modules.pullback j).mapIso EL ≪≫ (pullbackComp j r).app LK ≪≫
        (pullbackCongr h).app LK ≪≫ ((pullbackComp k g).app LK).symm ≪≫
        (Scheme.Modules.pullback k).mapIso E ≪≫ pullbackObjUnitIso k =
      (pullbackCongr hj).app L ≪≫ ((pullbackComp k f).app L).symm ≪≫
        (Scheme.Modules.pullback k).mapIso
          ((Scheme.Modules.pullback f).mapIso EL ≪≫ (pullbackComp f r).app LK ≪≫
            (pullbackCongr hf).app LK ≪≫ E) ≪≫ pullbackObjUnitIso k := by
  subst j
  subst g
  have hraw := primitive_refinement k f r h L LK EL E
  exact hraw.trans (erase_refinement (Scheme.Modules.pullback k)
    ((pullbackComp k f).app L).symm ((Scheme.Modules.pullback f).mapIso EL)
    ((pullbackComp f r).app LK) E (pullbackObjUnitIso k)).symm

end FrobeniusSplitting.RetainedCharacter
