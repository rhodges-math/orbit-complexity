import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareStacking
import Batteries.Tactic.Lint

/-! # Coframe squares on a restricted line

A coframe square on a whole chart can be compared through the original
line module. The comparison keeps the prescribed chart square and the
comparison of its scalar projection.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.CharacterLine

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem right_iso_eq {C : Type*} [Category C] {A B D : C}
    (x : A ⟶ D) (y : A ⟶ B) (e : B ≅ D) (h : x = y ≫ e.hom) :
    y = x ≫ e.inv := by
  rw [h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem comp_pair {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (M : D.Modules) :
    (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M ≫
        (pullbackCongr (Category.assoc f g h).symm).hom.app M := by
  have hc : (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      ((pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M) ≫
          (pullbackCongr (Category.assoc f g h)).hom.app M :=
    (pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app f g h M).trans
      (Category.assoc _ _ _).symm
  exact right_iso_eq _ _ ((pullbackCongr (Category.assoc f g h)).app M) hc

private theorem comp_pair_assoc {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (M : D.Modules)
    {N : A.Modules} (t : (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M ⟶ N) :
    (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M ≫ t =
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M ≫
        (pullbackCongr (Category.assoc f g h).symm).hom.app M ≫ t := by
  calc
    _ = ((pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M) ≫ t := (Category.assoc _ _ _).symm
    _ = _ := by rw [comp_pair]; simp only [Category.assoc]

private theorem congr_comp {A B C : Scheme.{u}} (f : A ⟶ B)
    {g h : B ⟶ C} (p : g = h) (M : C.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackCongr p).hom.app M) ≫
        (pullbackComp f h).hom.app M =
      (pullbackComp f g).hom.app M ≫
        (pullbackCongr (congrArg (fun k => f ≫ k) p)).hom.app M := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem congr_comp_assoc {A B C : Scheme.{u}} (f : A ⟶ B)
    {g h : B ⟶ C} (p : g = h) (M : C.Modules)
    {N : A.Modules} (t : (Scheme.Modules.pullback (f ≫ h)).obj M ⟶ N) :
    (Scheme.Modules.pullback f).map ((pullbackCongr p).hom.app M) ≫
        (pullbackComp f h).hom.app M ≫ t =
      (pullbackComp f g).hom.app M ≫
        (pullbackCongr (congrArg (fun k => f ≫ k) p)).hom.app M ≫ t := by
  calc
    _ = ((Scheme.Modules.pullback f).map ((pullbackCongr p).hom.app M) ≫
        (pullbackComp f h).hom.app M) ≫ t := (Category.assoc _ _ _).symm
    _ = _ := by rw [congr_comp]; simp only [Category.assoc]

private theorem map_component_inv_hom_assoc {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D)
    {G H : E ⥤ C} (η : G ≅ H) (M : E) {P : D} (t : F.obj (H.obj M) ⟶ P) :
    F.map (η.inv.app M) ≫ F.map (η.hom.app M) ≫ t = t :=
  Iso.inv_hom_id_map_assoc (η.app M) F t

private theorem rebase_prefix {Y YK P PK A B : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (a : A ⟶ PK) (b : B ⟶ P) (u : A ⟶ B)
    (hwhole : z ≫ f = g ≫ q) (hsmall : u ≫ b = a ≫ z)
    (htotal : u ≫ (b ≫ f) = (a ≫ g) ≫ q) (L : Y.Modules) :
    (pullbackComp a z).hom.app ((Scheme.Modules.pullback f).obj L) ≫
        (pullbackCongr hsmall.symm).hom.app ((Scheme.Modules.pullback f).obj L) ≫
        (pullbackComp u b).inv.app ((Scheme.Modules.pullback f).obj L) ≫
        (Scheme.Modules.pullback u).map ((pullbackComp b f).hom.app L) =
      (Scheme.Modules.pullback a).map
          ((pullbackComp z f).hom.app L ≫ (pullbackCongr hwhole).hom.app L ≫
            (pullbackComp g q).inv.app L) ≫
        (pullbackComp a g).hom.app ((Scheme.Modules.pullback q).obj L) ≫
        (pullbackComp (a ≫ g) q).hom.app L ≫
        (pullbackCongr htotal.symm).hom.app L ≫ (pullbackComp u (b ≫ f)).inv.app L := by
  have hpath : a ≫ (z ≫ f) = u ≫ (b ≫ f) :=
    (Category.assoc a z f).symm.trans
      ((congrArg (fun k => k ≫ f) hsmall.symm).trans (Category.assoc u b f))
  calc
    _ = (Scheme.Modules.pullback a).map ((pullbackComp z f).hom.app L) ≫
        (pullbackComp a (z ≫ f)).hom.app L ≫ (pullbackCongr hpath).hom.app L ≫
        (pullbackComp u (b ≫ f)).inv.app L := by
      rw [pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app,
        pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc, comp_pair_assoc]
      simp only [pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]
    _ = _ := by
      symm
      simp only [Functor.map_comp, Category.assoc]
      rw [comp_pair_assoc, map_component_inv_hom_assoc, congr_comp_assoc]
      simp only [pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]

private theorem paste_rebase {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N U : C} {P₀ P₁ P₂ Q₀ Q₁ Q₂ Q₃ W : D}
    (x₀ : P₀ ⟶ P₁) (x₁ : P₁ ⟶ P₂) (x₂ : P₂ ⟶ F.obj M)
    (m : M ⟶ N) (e : N ⟶ U) (w : F.obj U ⟶ W)
    (d₀ : P₀ ⟶ Q₀) (d₁ : Q₀ ⟶ Q₁) (d₂ : Q₁ ⟶ Q₂)
    (d₃ : Q₂ ⟶ Q₃) (d₄ : Q₃ ⟶ F.obj N)
    (hp : x₀ ≫ x₁ ≫ x₂ ≫ F.map m = d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄) :
    x₀ ≫ x₁ ≫ x₂ ≫ F.map (m ≫ e) ≫ w =
      d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ F.map e ≫ w := by
  calc
    _ = (x₀ ≫ x₁ ≫ x₂ ≫ F.map m) ≫ (F.map e ≫ w) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (d₀ ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄) ≫ (F.map e ≫ w) :=
      congrArg (fun t => t ≫ (F.map e ≫ w)) hp
    _ = _ := by simp only [Category.assoc]

/-- A coframe square for a restricted line agrees with the square for the
original line through the prescribed whole-chart comparison. -/
theorem squareFrameIso_rebase {Y YK P PK A B : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (a : A ⟶ PK) (b : B ⟶ P) (u : A ⟶ B)
    (hwhole : z ≫ f = g ≫ q) (hsmall : u ≫ b = a ≫ z)
    (htotal : u ≫ (b ≫ f) = (a ≫ g) ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback (b ≫ f)).obj L ≅ unitModule B) :
    squareFrameIso z a b u hsmall ((Scheme.Modules.pullback f).obj L)
        ((pullbackComp b f).app L ≪≫ E) =
      (Scheme.Modules.pullback a).mapIso
          ((pullbackComp z f).app L ≪≫ (pullbackCongr hwhole).app L ≪≫
            ((pullbackComp g q).app L).symm) ≪≫
        (pullbackComp a g).app ((Scheme.Modules.pullback q).obj L) ≪≫
        squareFrameIso q (a ≫ g) (b ≫ f) u htotal L E := by
  apply Iso.ext
  exact paste_rebase (Scheme.Modules.pullback u)
    ((pullbackComp a z).hom.app ((Scheme.Modules.pullback f).obj L))
    ((pullbackCongr hsmall.symm).hom.app ((Scheme.Modules.pullback f).obj L))
    ((pullbackComp u b).inv.app ((Scheme.Modules.pullback f).obj L))
    ((pullbackComp b f).hom.app L) E.hom (pullbackObjUnitIso u).hom
    ((Scheme.Modules.pullback a).map
      ((pullbackComp z f).hom.app L ≫ (pullbackCongr hwhole).hom.app L ≫
        (pullbackComp g q).inv.app L))
    ((pullbackComp a g).hom.app ((Scheme.Modules.pullback q).obj L))
    ((pullbackComp (a ≫ g) q).hom.app L) ((pullbackCongr htotal.symm).hom.app L)
    ((pullbackComp u (b ≫ f)).inv.app L)
    (rebase_prefix q f g z a b u hwhole hsmall htotal L)

end FrobeniusSplitting.CharacterLine
