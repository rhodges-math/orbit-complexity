import Mathlib.Topology.Sheaves.Module
import Batteries.Tactic.Lint

/-! # Components of modules on an open subset

The equivalence from modules on the site over an open subset to modules
on the open subspace acts on morphisms by evaluating at the corresponding
object of the over category.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace FrobeniusSplitting.OperatorSheaf

/-- The open-subspace module equivalence evaluates a morphism at the
corresponding object of the over category. -/
theorem overModuleEquiv_map_apply {X : TopCat.{u}} (U : TopologicalSpace.Opens X)
    (R : X.Sheaf RingCat.{u}) (M N : SheafOfModules.{u} (R.over U))
    (φ : M ⟶ N) (V : TopologicalSpace.Opens U)
    (x : M.val.obj (op (U.overEquivalence.inverse.obj V))) :
    (((U.sheafOfModulesEquivOver R).functor.map φ).val.app (op V)).hom x =
      (φ.val.app (op (U.overEquivalence.inverse.obj V))).hom x := by
  rfl

end FrobeniusSplitting.OperatorSheaf
