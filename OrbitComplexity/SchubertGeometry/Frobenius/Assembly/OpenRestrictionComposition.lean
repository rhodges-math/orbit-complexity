import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import OrbitComplexity.GroupActions.Modules.UnitCoherence
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Open restriction through a composition

The comparison from open restriction to pullback commutes with their two
composition isomorphisms. The adjunction calculation is carried out over
arbitrary schemes before any line or coefficient ring is substituted.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
namespace SchubertGeometry.ProjectiveCartier
universe u

open private transpose_composite
  from OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport

private theorem restrict_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (a : M ⟶ N) (U : X.Opens) :
    ((restrictFunctor f).map a).app U = a.app (f ''ᵁ U) := rfl

private theorem restrict_adjunct_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) :
    (restrictAdjunction f).homEquiv M ((Scheme.Modules.pullback f).obj M)
      ((restrictFunctorIsoPullback f).hom.app M) =
      (pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app
    (restrictAdjunction f) (pullbackPushforwardAdjunction f) M

private theorem conjugate_restrictComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  ext M U x
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Scheme.Modules.Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, restrictAdjunction_counit_app_app,
    restrictFunctorComp_hom_app_app, pushforwardComp_hom_app_app,
    CategoryTheory.Functor.comp_obj, restrict_map_app, pushforward_obj_presheaf_map]
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) x = x
  have hi (a : op ((f ≫ g) ⁻¹ᵁ U) ⟶ op ((f ≫ g) ⁻¹ᵁ U)) :
      M.presheaf.map a = 𝟙 _ := by
    rw [show a = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  erw [← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp]
  exact ConcreteCategory.congr_hom (hi _) x

private theorem double_restrict_adjunct {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) :
    ((restrictAdjunction g).comp (restrictAdjunction f)).homEquiv M
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
      ((restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M)) =
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app M := by
  rw [transpose_composite]
  rw [restrict_adjunct_hom, restrict_adjunct_hom]
  exact (Adjunction.comp_unit_app _ _ M).symm

/-- Open restriction and pullback have the same comparison on a composite
of open immersions, including their specified composition isomorphisms. -/
theorem restrictPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫ (pullbackComp f g).inv.app M =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) := by
  apply ((restrictAdjunction (f ≫ g)).homEquiv M
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))).injective
  have hl := (restrictAdjunction (f ≫ g)).homEquiv_naturality_right
    ((restrictFunctorIsoPullback (f ≫ g)).hom.app M) ((pullbackComp f g).inv.app M)
  rw [restrict_adjunct_hom] at hl
  have hp := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at hp
  have hr := Adjunction.homEquiv_conjugateEquiv
    ((restrictAdjunction g).comp (restrictAdjunction f))
    (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom
    ((restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
      (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M))
  rw [conjugate_restrictComp, double_restrict_adjunct] at hr
  exact hl.trans (hp.symm.trans hr)

end SchubertGeometry.ProjectiveCartier
