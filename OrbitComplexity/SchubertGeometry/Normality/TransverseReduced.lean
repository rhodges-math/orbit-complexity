import OrbitComplexity.GroupActions.Actions.ReducedIntersection
import OrbitComplexity.GroupActions.Varieties.Reduced.Retracts
import OrbitComplexity.GroupActions.Actions.Intersections
import OrbitComplexity.GroupActions.Rosenlicht.IntegralProducts
import OrbitComplexity.SchubertGeometry.Cells.OppositeActions
import OrbitComplexity.SchubertGeometry.FlagVariety.Transversality
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-! Reducedness of equivariant intersections under a smooth transverse action. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u



namespace SchubertGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The scheme-theoretic intersection of a Schubert variety and an opposite
Schubert variety is reduced. -/
theorem schubert_intersection_reduced (v w : G.weylGroup) :
    IsReduced (pullback (schubertInclusion G w) (oppositeSchubertInclusion G v)).left := by
  let X := (schubertVariety G w).toOver
  let Y := (oppositeSchubertVariety G v).toOver
  have : IsReduced (X ⊗ Y).left := by
    change IsReduced (pullback (schubertVariety G w).toSpec
      (oppositeSchubertVariety G v).toSpec)
    have := GroupActions.isIntegral_pullback_over_field
      (schubertVariety G w).toSpec (oppositeSchubertVariety G v).toSpec
    infer_instance
  have : IsLocallyNoetherian (X ⊗ Y).left := by
    change IsLocallyNoetherian (pullback (schubertVariety G w).toSpec
      (oppositeSchubertVariety G v).toSpec)
    infer_instance
  have := flagTransverseAction_smooth G
  exact GroupActions.reduced_equivariant_intersection
    (GroupActions.borelVariety G).toOver
    (GroupActions.oppositeBorelVariety G).toOver
    (flagVariety G).toOver X Y (schubertInclusion G w) (oppositeSchubertInclusion G v)

end SchubertGeometry
