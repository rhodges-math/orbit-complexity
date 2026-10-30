import OrbitComplexity.SchubertGeometry.FlagVariety.Action
import OrbitComplexity.GroupActions.Actions.StabilizerImages
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Varieties.BorelPoints

/-! # The Borel stabilizer of the base flag

The closed Borel subgroup identifies with the reduced stabilizer variety of the identity flag.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The rational flag represented by the identity of the reductive group. -/
def baseFlagPoint : (flagVariety G).points := flagVarietyPointsEquiv G (baseFlag G)

private theorem baseFlagPoint_fixed (g : G.points) :
    GroupActions.reductivePointsMulEquiv G g • baseFlagPoint G = baseFlagPoint G ↔
      g ∈ G.borelPoints := by
  rw [baseFlagPoint, flagVarietyAction_points, (flagVarietyPointsEquiv G).injective.eq_iff]
  rw [← MulAction.mem_stabilizer_iff, baseFlagStabilizer]

/-- The Borel variety has exactly the rational points stabilizing the base flag. -/
theorem borelInclusion_stabilizer :
    Set.range (GroupActions.Variety.mapPoints (GroupActions.borelInclusion G)) =
      (MulAction.stabilizer (GroupActions.reductiveVariety G).points (baseFlagPoint G) :
        Set (GroupActions.reductiveVariety G).points) := by
  ext p
  obtain ⟨g, rfl⟩ := (GroupActions.reductivePointsMulEquiv G).surjective p
  change _ ↔ GroupActions.reductivePointsMulEquiv G g • baseFlagPoint G = baseFlagPoint G
  rw [baseFlagPoint_fixed]
  constructor
  · rintro ⟨b, hb⟩
    have he : (GroupActions.borelPointsMulEquiv G b : G.points) = g :=
      (GroupActions.reductivePointsMulEquiv G).injective
        ((GroupActions.borelInclusion_points G b).symm.trans hb)
    exact he ▸ (GroupActions.borelPointsMulEquiv G b).property
  · intro hg
    let b : G.borelPoints := ⟨g, hg⟩
    refine ⟨(GroupActions.borelPointsMulEquiv G).symm b, ?_⟩
    rw [GroupActions.borelInclusion_points, MulEquiv.apply_symm_apply]
    rfl

private theorem borel_stabilizer_image :
    Set.range (GroupActions.Variety.mapPoints (GroupActions.borelInclusion G)) =
      Set.range (GroupActions.Variety.mapPoints
        (GroupActions.stabilizerInclusion (GroupActions.reductiveVariety G)
          (flagVariety G) (baseFlagPoint G))) :=
  (borelInclusion_stabilizer G).trans (GroupActions.stabilizerInclusion_points_range
    (GroupActions.reductiveVariety G) (flagVariety G) (baseFlagPoint G)).symm

/-- The Borel variety is the reduced stabilizer variety of the base flag. -/
def borelStabilizerIso :
    (GroupActions.borelVariety G).toOver ≅
      (GroupActions.stabilizerVariety (GroupActions.reductiveVariety G)
        (flagVariety G) (baseFlagPoint G)).toOver :=
  GroupActions.Variety.pointImageIso (GroupActions.borelInclusion G)
    (GroupActions.stabilizerInclusion (GroupActions.reductiveVariety G)
      (flagVariety G) (baseFlagPoint G)) (borel_stabilizer_image G)

/-- The Borel-stabilizer isomorphism commutes with inclusion in the reductive group. -/
theorem borelStabilizerIso_hom_comp :
    (borelStabilizerIso G).hom ≫
        GroupActions.stabilizerInclusion (GroupActions.reductiveVariety G)
          (flagVariety G) (baseFlagPoint G) = GroupActions.borelInclusion G :=
  GroupActions.Variety.pointImageIso_hom_comp _ _ (borel_stabilizer_image G)

end
end SchubertGeometry