import OrbitComplexity.SchubertGeometry.Deodhar.ParameterSteps

/-! # Coordinates of successive parameter varieties

The increasing-step identification retains each parameter coordinate and commutes with
projection from the parameters of the full word.
-/

open CategoryTheory AlgebraicGeometry GroupActions BruhatIntervals
open CartesianMonoidalCategory MonoidalCategory
attribute [local irreducible] SchubertGeometry.deodharPositiveStepIso
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- An increasing-step identification retains the coordinate at each old position. -/
theorem deodharPositiveStep_coord (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points)
    (j : deodharIndex G (expression.take n.val)) :
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
      (Variety.mapPoints (deodharParameterInclusion G (expression.take n.val))
        (Variety.mapPoints (deodharPositiveStepIso G expression n hn).hom x)) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints (deodharParameterInclusion G (expression.take (n.val + 1))) x)
        ((deodharStepIndexPositive G expression n hn).symm j) := by
  have hc : affineSpaceVarietyPointsEquiv K
      (deodharIndex G (expression.take n.val))
      (Variety.mapPoints ((deodharPositiveStepIso G expression n hn).hom ≫
        deodharParameterInclusion G (expression.take n.val)) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints (deodharParameterInclusion G (expression.take (n.val + 1))) x)
        ((deodharStepIndexPositive G expression n hn).symm j) := by
    unfold deodharPositiveStepIso
    exact coordinateReindexIso_points K (deodharStepIndexPositive G expression n hn)
      (deodharEqualPositions G (expression.take (n.val + 1)))
      (deodharEqualPositions G (expression.take n.val))
      (deodharEqualPositions_positive G expression n hn) x j
  have he := Variety.mapPoints_comp
    (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := deodharParameters G (expression.take n.val))
    (Z := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
    (deodharPositiveStepIso G expression n hn).hom
    (deodharParameterInclusion G (expression.take n.val)) x
  exact (congrArg (fun y => affineSpaceVarietyPointsEquiv K
    (deodharIndex G (expression.take n.val)) y j) he).symm.trans hc

/-- Increasing-step identification commutes with projection from the full parameters. -/
theorem deodharPositiveStep_projection (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharParameterProjection G expression (n.val + 1) ≫
        (deodharPositiveStepIso G expression n hn).hom =
      deodharParameterProjection G expression n.val := by
  apply Variety.mapPoints_injective (X := deodharParameters G expression)
    (Y := deodharParameters G (expression.take n.val))
  funext x
  apply Variety.mapPoints_injective_of_mono
    (X := deodharParameters G (expression.take n.val))
    (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
    (deodharParameterInclusion G (expression.take n.val))
  apply (affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))).injective
  funext j
  have hp := Variety.mapPoints_comp (X := deodharParameters G expression)
    (Y := deodharParameters G (expression.take (n.val + 1)))
    (Z := deodharParameters G (expression.take n.val))
    (deodharParameterProjection G expression (n.val + 1))
    (deodharPositiveStepIso G expression n hn).hom x
  have hc := deodharPositiveStep_coord G expression n hn
    (Variety.mapPoints (deodharParameterProjection G expression (n.val + 1)) x) j
  have hnew := deodharParameterProjection_coord G expression (n.val + 1) x
    ((deodharStepIndexPositive G expression n hn).symm j)
  have hold := deodharParameterProjection_coord G expression n.val x j
  have hi : deodharTakeIndex G expression (n.val + 1)
      ((deodharStepIndexPositive G expression n hn).symm j) =
      deodharTakeIndex G expression n.val j := by
    apply ULift.ext
    apply Subtype.ext
    apply Fin.ext
    exact deodharStepIndexPositive_val G expression n hn j
  have hcoord := congrArg (fun k => affineSpaceVarietyPointsEquiv K
    (deodharIndex G expression)
      (Variety.mapPoints (deodharParameterInclusion G expression) x) k) hi
  exact (congrArg (fun y => affineSpaceVarietyPointsEquiv K
    (deodharIndex G (expression.take n.val))
      (Variety.mapPoints (deodharParameterInclusion G (expression.take n.val)) y) j) hp).trans
        (hc.trans (hnew.trans (hcoord.trans hold.symm)))

end SchubertGeometry
