import OrbitComplexity.GroupActions.Actions.FromPoints
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Conjugation as an algebraic action

The categorical conjugation morphism gives a group variety an algebraic action on itself.
Its action on rational points is group conjugation.

## Main definitions

* `GroupActions.Variety.conjugationAction`: the algebraic conjugation action.

## Main results

* `GroupActions.Variety.conjugationAction_smul`: the conjugation formula on rational points.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (H : GroupActions.Variety K) [GrpObj H.toOver]

/-- Conjugation defines an algebraic action of a group variety on itself. -/
@[instance_reducible]
def conjugationAction : ModObj H.toOver H.toOver := by
  letI : MulAction H.points H.points :=
    MulAction.compHom H.points (ConjAct.toConjAct (G := H.points)).toMonoidHom
  refine modObjOfPoints H H (GrpObj.conj H.toOver) ?_
  intro h x
  rw [GrpObj.lift_conj_eq_mul_mul_inv]
  change H.pointsEquivOverHom h * H.pointsEquivOverHom x *
      (H.pointsEquivOverHom h)⁻¹ = H.pointsEquivOverHom (h * x * h⁻¹)
  rw [pointsEquivOverHom_mul, pointsEquivOverHom_mul, pointsEquivOverHom_inv]

/-- The algebraic conjugation action conjugates rational group points. -/
theorem conjugationAction_smul (h x : H.points) :
    letI := conjugationAction H
    letI : SMul H.points H.points := (pointsMulAction H H).toSMul
    h • x = h * x * h⁻¹ := by
  let := conjugationAction H
  let : SMul H.points H.points := (pointsMulAction H H).toSMul
  apply H.pointsEquivOverHom.injective
  change H.pointsEquivOverHom (H.pointsEquivOverHom.symm
    (lift (H.pointsEquivOverHom h) (H.pointsEquivOverHom x) ≫ GrpObj.conj H.toOver)) =
      H.pointsEquivOverHom (h * x * h⁻¹)
  rw [Equiv.apply_symm_apply, GrpObj.lift_conj_eq_mul_mul_inv, pointsEquivOverHom_mul,
    pointsEquivOverHom_mul, pointsEquivOverHom_inv]

end

end GroupActions.Variety
