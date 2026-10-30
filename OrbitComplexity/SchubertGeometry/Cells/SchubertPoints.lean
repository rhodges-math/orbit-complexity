import OrbitComplexity.SchubertGeometry.Cells.Schubert
import OrbitComplexity.SchubertGeometry.Cells.Bruhat

/-! # Rational points of Schubert cells

The Borel orbit description agrees with Bruhat double cosets modulo the Borel.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The rational image of a Schubert cell is the Borel orbit of its Weyl flag. -/
theorem schubertCell_points_range (w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) =
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (GroupActions.orbitPointsEquiv (GroupActions.borelVariety G) (flagVariety G)
      (weylFlagPoint G w) z).property
  · intro hp
    obtain ⟨z, hz⟩ := (GroupActions.orbitPointsEquiv (GroupActions.borelVariety G)
      (flagVariety G) (weylFlagPoint G w)).surjective ⟨p, hp⟩
    exact ⟨z, congrArg Subtype.val hz⟩

/-- Membership in a Schubert orbit is membership of its representative in the double coset. -/
theorem mem_schubertOrbit_iff (w : G.weylGroup) (g : G.points) :
    flagVarietyPointsEquiv G (flagProjection G g) ∈
        MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w) ↔
      g ∈ ReductiveGroups.subgroupDoubleCoset G.borelPoints (G.weylPoint w) := by
  constructor
  · intro hg
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hg
    rw [weylFlagPoint, borelFlag_smul] at hb
    have he := (flagVarietyPointsEquiv G).injective hb
    have hc : ((GroupActions.borelPointsMulEquiv G b : G.points) * G.weylPoint w)⁻¹ * g ∈
        G.borelPoints := (flagProjection_eq_iff G _ _).mp he
    refine ⟨GroupActions.borelPointsMulEquiv G b,
      (GroupActions.borelPointsMulEquiv G b).property, _, hc, ?_⟩
    group
  · rintro ⟨b, hb, c, hc, rfl⟩
    let p := (GroupActions.borelPointsMulEquiv G).symm ⟨b, hb⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨p, ?_⟩
    rw [weylFlagPoint, borelFlag_smul]
    apply congrArg (flagVarietyPointsEquiv G)
    change flagProjection G ((GroupActions.borelPointsMulEquiv G p : G.points) *
      G.weylPoint w) = flagProjection G (b * G.weylPoint w * c)
    have hp : (GroupActions.borelPointsMulEquiv G p : G.points) = b := by
      exact congrArg Subtype.val ((GroupActions.borelPointsMulEquiv G).apply_symm_apply ⟨b, hb⟩)
    rw [hp]
    apply (flagProjection_eq_iff G _ _).mpr
    simpa only [inv_mul_cancel_left] using hc

/-- Every rational flag belongs to a Schubert cell's Borel orbit. -/
theorem schubertOrbits_cover (x : (flagVariety G).points) :
    ∃ w : G.weylGroup,
      x ∈ MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w) := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  obtain ⟨w, hw⟩ := bruhatDecomposition G g
  exact ⟨w, (mem_schubertOrbit_iff G w g).mpr hw⟩

/-- A rational flag belongs to at most one Schubert cell's Borel orbit. -/
theorem schubertOrbits_disjoint {v w : G.weylGroup} {x : (flagVariety G).points}
    (hv : x ∈ MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G v))
    (hw : x ∈ MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w)) :
    v = w := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  exact bruhatDecomposition_unique G ((mem_schubertOrbit_iff G v g).mp hv)
    ((mem_schubertOrbit_iff G w g).mp hw)

end
end SchubertGeometry
