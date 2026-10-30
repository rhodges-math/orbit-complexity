import OrbitComplexity.GroupActions.Actions.Points

/-! # Right translations of a group variety

Multiplication on the right by a rational point is an isomorphism of the group variety.
Its map on rational points is right multiplication in the rational-point group.

## Main definitions

* `GroupActions.rightTranslation`: the right-translation isomorphism.

## Main results

* `GroupActions.rightTranslation_points`: the rational-point multiplication formula.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H : Variety K) [GrpObj H.toOver]

/-- Right translation by a rational point is an isomorphism of the group variety. -/
def rightTranslation (h : H.points) : H.toOver ≅ H.toOver :=
  GrpObj.mulRight (H.pointsEquivOverHom h)

/-- Right translation on rational points is multiplication on the right. -/
theorem rightTranslation_points (h k : H.points) :
    Variety.mapPoints (rightTranslation H h).hom k = k * h := by
  apply H.pointsEquivOverHom.injective
  change H.pointsEquivOverHom k ≫ (rightTranslation H h).hom =
    H.pointsEquivOverHom (k * h)
  rw [Variety.pointsEquivOverHom_mul]
  have ht : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) =
      𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  simp [rightTranslation, GrpObj.mulRight, Hom.mul_def, comp_lift_assoc, ht]

end

end GroupActions
