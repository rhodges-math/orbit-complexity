import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.PriorSectionNormalization
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficients obtained by evaluating coframes

A whole coframe equation is evaluated over an arbitrary scheme. Its inverse
then gives the corresponding line-frame coefficient, before any chart or
character module is substituted.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
namespace SchubertGeometry.ProjectiveCartier
universe u

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A section whose coframe coordinate is multiplication by a scalar is
that scalar times the inverse coframe evaluated at one. -/
theorem coframe_section_value {X : Scheme.{u}} (M : X.Modules)
    (s : unitModule X ⟶ M) (E : M ≅ unitModule X) (a : Γ(X, ⊤))
    (hs : s ≫ E.hom = globalSectionsSmul (unitModule X) a) :
    (s.app ⊤ (1 : Γ(X, ⊤)) : Γ(M, ⊤)) =
      a • (E.inv.app ⊤ (1 : Γ(X, ⊤)) : Γ(M, ⊤)) := by
  have hmul : ((globalSectionsSmul (unitModule X) a).val.app (op ⊤)).hom
      (1 : Γ(X, ⊤)) = a := by
    change (globalSectionsSmul (unitModule X) a).app ⊤ (1 : Γ(X, ⊤)) = a
    rw [globalSectionsSmul_app]
    have hi : (⊤ : X.Opens).leTop.op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hi, CategoryTheory.Functor.map_id]
    change a * 1 = a
    exact mul_one a
  have hwhole : s = globalSectionsSmul (unitModule X) a ≫ E.inv := by
    calc
      s = (s ≫ E.hom) ≫ E.inv := by
        rw [Category.assoc, E.hom_inv_id, Category.comp_id]
      _ = globalSectionsSmul (unitModule X) a ≫ E.inv :=
        congrArg (fun t : unitModule X ⟶ unitModule X => t ≫ E.inv) hs
  have hv := congrArg
    (fun t : unitModule X ⟶ M => (t.app ⊤ (1 : Γ(X, ⊤)) : Γ(M, ⊤))) hwhole
  change (s.app ⊤ (1 : Γ(X, ⊤)) : Γ(M, ⊤)) =
    (E.inv.val.app (op ⊤)).hom
      (((globalSectionsSmul (unitModule X) a).val.app (op ⊤)).hom (1 : Γ(X, ⊤))) at hv
  rw [hmul] at hv
  have hlin := Scheme.Modules.Hom.app_smul E.inv a (1 : Γ(X, ⊤))
  change E.inv.app ⊤ (a * 1 : Γ(X, ⊤)) =
    a • (E.inv.app ⊤ (1 : Γ(X, ⊤)) : Γ(M, ⊤)) at hlin
  exact hv.trans ((congrArg (fun z : Γ(X, ⊤) => E.inv.app ⊤ z)
    (mul_one a).symm).trans hlin)

end SchubertGeometry.ProjectiveCartier
