import OrbitComplexity.GroupActions.Varieties.Morphisms
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Rational points of algebraic group actions

A group object over a field gives a group on its rational points. An action morphism gives
an action of this group on the rational points of the variety.

## Main definitions

* `GroupActions.Variety.pointsGroup`: the group on rational points of a group variety.
* `GroupActions.Variety.pointsMulAction`: the action induced on rational points.

## Main results

* `GroupActions.Variety.pointsEquivOverHom_smul`: the action is composition with the
  action morphism.

## Implementation notes

Algebraic actions use `CategoryTheory.ModObj` in the category of schemes over the base field.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Rational points of a group variety form a group. -/
instance pointsGroup (H : GroupActions.Variety K) [GrpObj H.toOver] : Group H.points :=
  H.pointsEquivOverHom.group

/-- The unit rational point corresponds to the unit morphism of the group object. -/
theorem pointsEquivOverHom_one (H : GroupActions.Variety K) [GrpObj H.toOver] :
    H.pointsEquivOverHom 1 = 1 := H.pointsEquivOverHom.mulEquiv.map_one

/-- Multiplication of rational points corresponds to multiplication of morphisms. -/
theorem pointsEquivOverHom_mul (H : GroupActions.Variety K) [GrpObj H.toOver]
    (h k : H.points) : H.pointsEquivOverHom (h * k) =
      H.pointsEquivOverHom h * H.pointsEquivOverHom k := H.pointsEquivOverHom.mulEquiv.map_mul h k

/-- Inversion of rational points corresponds to inversion of morphisms. -/
theorem pointsEquivOverHom_inv (H : GroupActions.Variety K) [GrpObj H.toOver]
    (h : H.points) : H.pointsEquivOverHom h⁻¹ = (H.pointsEquivOverHom h)⁻¹ :=
  H.pointsEquivOverHom.mulEquiv.map_inv h

/-- Rational points of an algebraic action carry the induced group action. -/
instance pointsMulAction (H X : GroupActions.Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] : MulAction H.points X.points := by
  letI : MulAction H.points (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X.toOver) :=
    MulAction.compHom _ H.pointsEquivOverHom.mulEquiv.toMonoidHom
  exact X.pointsEquivOverHom.mulAction H.points

/-- The action on rational points agrees with the action on morphisms from the base. -/
theorem pointsEquivOverHom_smul (H X : GroupActions.Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (h : H.points) (x : X.points) :
    X.pointsEquivOverHom (h • x) = H.pointsEquivOverHom h • X.pointsEquivOverHom x := by
  exact X.pointsEquivOverHom.apply_symm_apply _

end

end GroupActions.Variety
