import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.Lint

/-!
# Reflection of line coframes

Injectivity on global functions reflects equality of coframes of the same
line module. The comparison is made over arbitrary schemes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def unitApply {X : Scheme.{u}} (h : unitModule X ⟶ unitModule X)
    (U : X.Opens) (r : Γ(X, U)) : Γ(X, U) :=
  h.app U r

private theorem unitApply_mul {X : Scheme.{u}}
    (h : unitModule X ⟶ unitModule X) (U : X.Opens) (r s : Γ(X, U)) :
    unitApply h U (r * s) = r * unitApply h U s :=
  h.app_smul r s

private theorem unitApply_smul {X : Scheme.{u}}
    (c : Γ(X, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    unitApply (globalSectionsSmul (unitModule X) c) U r =
      X.presheaf.map U.leTop.op c * r := by
  have h := congrArg
    (fun k : Γ(unitModule X, U) ⟶ Γ(unitModule X, U) => k r)
    (globalSectionsSmul_app (unitModule X) c U)
  exact h

private def unitValue {X : Scheme.{u}} (h : unitModule X ⟶ unitModule X) :
    Γ(X, ⊤) :=
  unitApply h ⊤ 1

private theorem unitValue_restrict {X : Scheme.{u}}
    (h : unitModule X ⟶ unitModule X) (U : X.Opens) :
    unitApply h U 1 =
      X.presheaf.map U.leTop.op (unitValue h) := by
  have hn : unitApply h U (X.presheaf.map U.leTop.op (1 : Γ(X, ⊤))) =
      X.presheaf.map U.leTop.op (unitValue h) := by
    exact congrArg
      (fun k : Γ(unitModule X, ⊤) ⟶ Γ(unitModule X, U) =>
        k (1 : Γ(X, ⊤)))
      (h.mapPresheaf.naturality U.leTop.op)
  rw [map_one] at hn
  exact hn

private theorem unit_hom_ext {X : Scheme.{u}}
    (h k : unitModule X ⟶ unitModule X) (heq : unitValue h = unitValue k) :
    h = k := by
  apply Scheme.Modules.hom_ext
  intro U
  have hone : unitApply h U 1 = unitApply k U 1 := by
    rw [unitValue_restrict, unitValue_restrict, heq]
  have hfun : ∀ r : Γ(X, U), unitApply h U r = unitApply k U r := by
    intro r
    calc
      unitApply h U r = r * unitApply h U 1 := by
        have hh := unitApply_mul h U r 1
        rw [mul_one] at hh
        exact hh
      _ = r * unitApply k U 1 := congrArg (fun t : Γ(X, U) => r * t) hone
      _ = unitApply k U r := by
        have hk := unitApply_mul k U r 1
        rw [mul_one] at hk
        exact hk.symm
  ext r
  exact hfun r

private theorem restrict_top {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    X.presheaf.map (⊤ : X.Opens).leTop.op r = r := by
  have h : (⊤ : X.Opens).leTop = 𝟙 (⊤ : X.Opens) := Subsingleton.elim _ _
  rw [h, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem unitValue_smul {X : Scheme.{u}} (c : Γ(X, ⊤)) :
    unitValue (globalSectionsSmul (unitModule X) c) = c := by
  change unitApply (globalSectionsSmul (unitModule X) c) ⊤ 1 = c
  rw [unitApply_smul, restrict_top, mul_one]

private theorem unit_hom_eq_smul {X : Scheme.{u}}
    (h : unitModule X ⟶ unitModule X) :
    h = globalSectionsSmul (unitModule X) (unitValue h) := by
  apply unit_hom_ext
  exact (unitValue_smul (unitValue h)).symm

private theorem conjugate_smul {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (c : Γ(X, ⊤)) :
    e.inv ≫ globalSectionsSmul M c ≫ e.hom = globalSectionsSmul N c := by
  calc
    e.inv ≫ globalSectionsSmul M c ≫ e.hom =
        e.inv ≫ (e.hom ≫ globalSectionsSmul N c) :=
      congrArg (fun t : M ⟶ N => e.inv ≫ t) (globalSectionsSmul_naturality e.hom c)
    _ = globalSectionsSmul N c := by rw [Iso.inv_hom_id_assoc]

private theorem pullback_unit_hom_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : Function.Injective f.appTop.hom) :
    Function.Injective (fun h : unitModule Y ⟶ unitModule Y =>
      (Scheme.Modules.pullback f).map h) := by
  intro h k heq
  apply unit_hom_ext
  apply hinj
  have hh := unit_hom_eq_smul h
  have hk := unit_hom_eq_smul k
  change (Scheme.Modules.pullback f).map h = (Scheme.Modules.pullback f).map k at heq
  have hhmap := congrArg (fun t : unitModule Y ⟶ unitModule Y =>
    (Scheme.Modules.pullback f).map t) hh
  have hkmap := congrArg (fun t : unitModule Y ⟶ unitModule Y =>
    (Scheme.Modules.pullback f).map t) hk
  change (Scheme.Modules.pullback f).map h =
    (Scheme.Modules.pullback f).map (globalSectionsSmul (unitModule Y) (unitValue h)) at hhmap
  change (Scheme.Modules.pullback f).map k =
    (Scheme.Modules.pullback f).map (globalSectionsSmul (unitModule Y) (unitValue k)) at hkmap
  rw [pullback_map_globalSectionsSmul] at hhmap hkmap
  have hc := congrArg
    (fun t => (pullbackObjUnitIso f).inv ≫ t ≫ (pullbackObjUnitIso f).hom)
    (hhmap.symm.trans (heq.trans hkmap))
  have hs :
      globalSectionsSmul (unitModule X) (f.appTop (unitValue h)) =
        globalSectionsSmul (unitModule X) (f.appTop (unitValue k)) := by
    exact (conjugate_smul (pullbackObjUnitIso f) (f.appTop (unitValue h))).symm.trans
      (hc.trans (conjugate_smul (pullbackObjUnitIso f) (f.appTop (unitValue k))))
  have hv := congrArg (fun t : unitModule X ⟶ unitModule X => unitValue t) hs
  rw [unitValue_smul, unitValue_smul] at hv
  exact hv

/-- Injectivity on global functions reflects equality of pulled-back line coframes. -/
theorem frame_eq_of_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (E F : L ≅ unitModule Y)
    (hinj : Function.Injective f.appTop.hom)
    (heq : (Scheme.Modules.pullback f).mapIso E ≪≫ pullbackObjUnitIso f =
      (Scheme.Modules.pullback f).mapIso F ≪≫ pullbackObjUnitIso f) :
    E = F := by
  have hh : (Scheme.Modules.pullback f).map E.hom =
      (Scheme.Modules.pullback f).map F.hom := by
    apply (cancel_mono (pullbackObjUnitIso f).hom).mp
    exact congrArg Iso.hom heq
  have hc : (Scheme.Modules.pullback f).map (E.inv ≫ F.hom) =
      (Scheme.Modules.pullback f).map (𝟙 (unitModule Y)) := by
    rw [Functor.map_comp, ← hh, ← Functor.map_comp, E.inv_hom_id]
  have hEF : E.inv ≫ F.hom = 𝟙 (unitModule Y) :=
    pullback_unit_hom_injective f hinj hc
  apply Iso.ext
  calc
    E.hom = E.hom ≫ (E.inv ≫ F.hom) := by rw [hEF, Category.comp_id]
    _ = F.hom := by rw [Iso.hom_inv_id_assoc]

/-- The ratio of two affine coframes gives their whole module-map comparison. -/
theorem affineCoframeUnit_hom (A : Type u) [CommRing A]
    {L : (Spec (.of A)).Modules} (E F : L ≅ unitModule (Spec (.of A))) :
    F.hom = E.hom ≫ globalSectionsSmul (unitModule (Spec (.of A)))
      ((Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A)) := by
  have hc : unitValue (E.inv ≫ F.hom) =
      (Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A) := by
    rw [affineCoframeUnit_value]
    have hi := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).hom_inv_id
      (unitValue (E.inv ≫ F.hom))
    exact hi.symm
  calc
    F.hom = E.hom ≫ (E.inv ≫ F.hom) := by rw [Iso.hom_inv_id_assoc]
    _ = E.hom ≫ globalSectionsSmul (unitModule (Spec (.of A)))
        (unitValue (E.inv ≫ F.hom)) :=
      congrArg (fun t : unitModule (Spec (.of A)) ⟶ unitModule (Spec (.of A)) =>
        E.hom ≫ t) (unit_hom_eq_smul (E.inv ≫ F.hom))
    _ = E.hom ≫ globalSectionsSmul (unitModule (Spec (.of A)))
        ((Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A)) := by rw [hc]

end FrobeniusSplitting.RetainedCharacter
