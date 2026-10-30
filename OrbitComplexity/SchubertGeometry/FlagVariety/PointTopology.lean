import OrbitComplexity.SchubertGeometry.FlagVariety.Variety
import OrbitComplexity.SchubertGeometry.FlagVariety.QuotientOpen
import OrbitComplexity.GroupActions.Varieties.OpenPointMaps

/-! # The topology of rational flag points

The Borel-coset point equivalence identifies the quotient and scheme Zariski topologies.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem quotientPoints_comp :
    (flagVarietyPointsEquiv G : flagPoints G → (flagVariety G).points) ∘ flagProjection G =
      GroupActions.Variety.mapPoints (flagQuotientMorphism G) ∘
        GroupActions.reductivePointsHomeomorph G :=
  funext (fun g => (flagQuotientMorphism_points G g).symm)

private theorem flagPointsContinuous : Continuous (flagVarietyPointsEquiv G) := by
  apply (flagProjection_quotientMap G).continuous_iff.mpr
  rw [quotientPoints_comp]
  exact (GroupActions.Variety.continuous_mapPoints (flagQuotientMorphism G)).comp
    (GroupActions.reductivePointsHomeomorph G).continuous

private theorem flagPointsOpen : IsOpenMap (flagVarietyPointsEquiv G) := by
  apply IsOpenMap.of_comp (continuous_flagProjection G) (flagProjection_surjective G)
  rw [quotientPoints_comp]
  exact (GroupActions.Variety.isOpenMap_mapPoints (flagQuotientMorphism G)
    (flagQuotient_isOpenMap G)).comp (GroupActions.reductivePointsHomeomorph G).isOpenMap

/-- The quotient Zariski topology on Borel cosets equals the flag variety point topology. -/
def flagVarietyPointsHomeomorph : flagPoints G ≃ₜ (flagVariety G).points :=
  (flagVarietyPointsEquiv G).toHomeomorphOfContinuousOpen
    (flagPointsContinuous G) (flagPointsOpen G)

end
end SchubertGeometry