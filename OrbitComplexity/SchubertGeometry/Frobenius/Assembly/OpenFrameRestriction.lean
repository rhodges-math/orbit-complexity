import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenRestrictionComposition
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.PriorSectionNormalization
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Line frames under open refinement

Inverse coframes give line sections on their open ranges. Pulling back a
coframe along an open refinement gives the restriction of this same section.
The comparison includes the pullback composition isomorphism.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
namespace SchubertGeometry.ProjectiveCartier
universe u

open private restrict_map_app
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenRestrictionComposition

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def imageSectionAt {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (U : X.Opens) (x : Γ((Scheme.Modules.pullback j).obj M, U)) :
    Γ(M, j ''ᵁ U) :=
  (M.restrictAppIso j U).hom
    (((restrictFunctorIsoPullback j).inv.app M).app U x)

private theorem imageSectionAt_natural {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) {U V : X.Opens} (h : V ≤ U)
    (x : Γ((Scheme.Modules.pullback j).obj M, U)) :
    imageSectionAt j M V
        (((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE h).op x) =
      M.presheaf.map (homOfLE (j.image_mono h)).op (imageSectionAt j M U x) := by
  have hn := ConcreteCategory.congr_hom
    (((restrictFunctorIsoPullback j).inv.app M).mapPresheaf.naturality (homOfLE h).op) x
  have hr := ConcreteCategory.congr_hom
    (Scheme.Modules.map_restrictAppIso_hom j M (homOfLE h).op)
    (((restrictFunctorIsoPullback j).inv.app M).app U x)
  exact (congrArg (fun z => (M.restrictAppIso j V).hom z) hn).trans hr

private theorem imageSectionAt_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) (U : X.Opens)
    (x : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M), U)) :
    imageSectionAt (f ≫ g) M U (((pullbackComp f g).hom.app M).app U x) =
      M.presheaf.map (eqToHom (by simp : (f ≫ g) ''ᵁ U = g ''ᵁ (f ''ᵁ U))).op
        (imageSectionAt g M (f ''ᵁ U)
          (imageSectionAt f ((Scheme.Modules.pullback g).obj M) U x)) := by
  have hIso : (restrictFunctorIsoPullback (f ≫ g)).app M ≪≫
        ((pullbackComp f g).app M).symm =
      (restrictFunctorComp f g).app M ≪≫
        (restrictFunctor f).mapIso ((restrictFunctorIsoPullback g).app M) ≪≫
          (restrictFunctorIsoPullback f).app ((Scheme.Modules.pullback g).obj M) :=
    Iso.ext (restrictPullback_comp f g M)
  have hi := congrArg Iso.inv hIso
  have hv := congrArg
    (fun t : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶
      (restrictFunctor (f ≫ g)).obj M => t.app U x) hi
  change (((pullbackComp f g).hom.app M) ≫
      (restrictFunctorIsoPullback (f ≫ g)).inv.app M).app U x =
    ((restrictFunctorIsoPullback f).inv.app ((Scheme.Modules.pullback g).obj M) ≫
      (restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app M) ≫
        (restrictFunctorComp f g).inv.app M).app U x at hv
  simp only [Scheme.Modules.Hom.comp_app, restrict_map_app,
    restrictFunctorComp_inv_app_app] at hv
  exact hv

private theorem range_comp_le {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    (f ≫ g).opensRange ≤ g.opensRange := by
  rintro z ⟨x, rfl⟩
  exact ⟨f x, rfl⟩

/-- The inverse coframe, evaluated at one, is a line section on the open
range, with the image-open equality transported separately. -/
def openFrameSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (E : (Scheme.Modules.pullback j).obj M ≅ unitModule X) :
    Γ(M, j.opensRange) :=
  M.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op
    (imageSectionAt j M ⊤ (E.inv.app ⊤ (1 : Γ(X, ⊤))))

private def compositeFrame {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (E : (Scheme.Modules.pullback g).obj M ≅ unitModule Y) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ unitModule X :=
  ((pullbackComp f g).app M).symm ≪≫ (Scheme.Modules.pullback f).mapIso E ≪≫
    pullbackObjUnitIso f

/-- The line section of the pulled-back coframe is the restriction of the
line section of the preceding coframe. -/
theorem openFrameSection_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) (E : (Scheme.Modules.pullback g).obj M ≅ unitModule Y) :
    openFrameSection (f ≫ g) M (compositeFrame f g M E) =
      M.presheaf.map (homOfLE (range_comp_le f g)).op (openFrameSection g M E) := by
  let v : Γ((Scheme.Modules.pullback g).obj M, ⊤) := E.inv.app ⊤ (1 : Γ(Y, ⊤))
  let t : unitModule X ⟶ (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj M) :=
    (pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map E.inv
  have hp := imageSection_pullSection f ((Scheme.Modules.pullback g).obj M) E.inv
  change imageSectionAt f ((Scheme.Modules.pullback g).obj M) ⊤
      (t.app ⊤ (1 : Γ(X, ⊤))) =
    ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE le_top).op v at hp
  have hc := imageSectionAt_comp f g M ⊤ (t.app ⊤ (1 : Γ(X, ⊤)))
  have hn := imageSectionAt_natural g M (le_top : f ''ᵁ (⊤ : X.Opens) ≤ ⊤) v
  have hm := hc.trans
    ((congrArg (fun z =>
      M.presheaf.map (eqToHom (by simp : (f ≫ g) ''ᵁ (⊤ : X.Opens) =
        g ''ᵁ (f ''ᵁ (⊤ : X.Opens)))).op
          (imageSectionAt g M (f ''ᵁ (⊤ : X.Opens)) z)) hp).trans
      (congrArg (fun z => M.presheaf.map
        (eqToHom (by simp : (f ≫ g) ''ᵁ (⊤ : X.Opens) =
          g ''ᵁ (f ''ᵁ (⊤ : X.Opens)))).op z) hn))
  change M.presheaf.map (eqToHom (f ≫ g).image_top_eq_opensRange.symm).op
      (imageSectionAt (f ≫ g) M ⊤
        (((pullbackComp f g).hom.app M).app ⊤ (t.app ⊤ (1 : Γ(X, ⊤))))) = _
  rw [hm]
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _)
      (imageSectionAt g M ⊤ v) =
    (M.presheaf.map _ ≫ M.presheaf.map _) (imageSectionAt g M ⊤ v)
  erw [← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg M.presheaf.map (Subsingleton.elim _ _)) (imageSectionAt g M ⊤ v)

private theorem range_triangle_le {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : X ⟶ Z) (h : f ≫ g = j)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion j] :
    j.opensRange ≤ g.opensRange := by
  subst j
  exact range_comp_le f g

/-- A commuting triangle of open immersions retains the original range
section when the coframe is pulled back through the specified triangle. -/
theorem openFrameSection_triangle {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : X ⟶ Z) (h : f ≫ g = j)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion j]
    (M : Z.Modules) (E : (Scheme.Modules.pullback g).obj M ≅ unitModule Y) :
    openFrameSection j M
        ((pullbackCongr h.symm).app M ≪≫ compositeFrame f g M E) =
      M.presheaf.map (homOfLE (range_triangle_le f g j h)).op
        (openFrameSection g M E) := by
  subst j
  have hr : (Iso.refl (Scheme.Modules.pullback (f ≫ g))).app M =
      Iso.refl ((Scheme.Modules.pullback (f ≫ g)).obj M) := rfl
  simpa only [pullbackCongr, eqToIso_refl, hr, Iso.refl_trans] using
    openFrameSection_comp f g M E

end SchubertGeometry.ProjectiveCartier
