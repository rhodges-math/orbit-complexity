import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Batteries.Tactic.Lint

/-! # Components of open module restriction comparisons

The comparison between modules on an open subset and restricted modules
acts by the identity on sections. The corresponding comparison of unit
modules preserves the unit section.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace SchubertGeometry.ProjectiveCartier

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The comparison to scheme restriction preserves the underlying section. -/
theorem overFunctorEquiv_hom_apply {X : Scheme.{u}} (U : X.Opens) (L : X.Modules)
    (V : U.toScheme.Opens)
    (x : Γ((overEquiv U).functor.obj (L.over U), V)) :
    ((overFunctorEquiv U).hom.app L).app V x = x := by
  rfl

/-- The inverse comparison from scheme restriction preserves the underlying section. -/
theorem overFunctorEquiv_inv_apply {X : Scheme.{u}} (U : X.Opens) (L : X.Modules)
    (V : U.toScheme.Opens) (x : Γ(L.restrict U.ι, V)) :
    ((overFunctorEquiv U).inv.app L).app V x = x := by
  rfl

/-- The inverse unit comparison sends the unit section to the unit section. -/
theorem restrictUnitIso_inv_one {X : Scheme.{u}} (U : X.Opens)
    (V : U.toScheme.Opens) :
    (restrictUnitIso U.ι).inv.app V (1 : Γ(U.toScheme, V)) =
      (1 : Γ(X, U.ι ''ᵁ V)) := by
  change (U.ι.appIso V).inv (1 : Γ(U.toScheme, V)) = 1
  exact map_one (U.ι.appIso V).inv.hom

end SchubertGeometry.ProjectiveCartier
