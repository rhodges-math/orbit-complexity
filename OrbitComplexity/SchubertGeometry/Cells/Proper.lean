import OrbitComplexity.SchubertGeometry.FlagVariety.Proper
import OrbitComplexity.SchubertGeometry.Cells.Richardson

/-! # Proper Schubert and Richardson varieties

Their closed immersions into the flag variety give proper structure morphisms.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- A Schubert variety is proper over its coefficient field. -/
instance schubertVariety_isProper (w : G.weylGroup) :
    IsProper (schubertVariety G w).toSpec := by
  change IsProper (schubertVariety G w).toOver.hom
  rw [← (schubertInclusion G w).w]
  change IsProper ((schubertInclusion G w).left ≫ (flagVariety G).toSpec)
  infer_instance

/-- A closed Richardson variety is proper over its coefficient field. -/
instance richardsonVariety_isProper (u w : G.weylGroup) :
    IsProper (richardsonVariety G u w).toSpec := by
  change IsProper (richardsonVariety G u w).toOver.hom
  rw [← (richardsonInclusion G u w).w]
  change IsProper ((richardsonInclusion G u w).left ≫ (flagVariety G).toSpec)
  infer_instance

end SchubertGeometry
