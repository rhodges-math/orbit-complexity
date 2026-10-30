import OrbitComplexity.SchubertGeometry.Cells.RootFactors
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootConjugation

/-! # Unique root coordinates of rational Schubert points

Inversion-root points give exactly the flags of their Schubert cell, without repetitions.
-/

open ReductiveGroups

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The inversion-root subgroup in the group of reductive rational points. -/
abbrev schubertUnipotentPoints (w : G.weylGroup) : Subgroup G.points :=
  G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

/-- The rational flag obtained from an inversion-root point and its Weyl representative. -/
def schubertPointMap (w : G.weylGroup) (u : schubertUnipotentPoints G w) : flagPoints G :=
  flagProjection G ((u : G.points) * G.weylPoint w)

/-- Inversion-root points have distinct flags in their Schubert cell. -/
theorem schubertPointMap_injective (w : G.weylGroup) :
    Function.Injective (schubertPointMap G w) := by
  intro a b hab
  have hB := (flagProjection_eq_iff G _ _).mp hab
  have hU := G.inversionPoints_conj_opposite w ((a : G.points)⁻¹ * b)
    ((schubertUnipotentPoints G w).mul_mem
      ((schubertUnipotentPoints G w).inv_mem a.property) b.property)
  have hB' : (G.weylPoint w)⁻¹ * ((a : G.points)⁻¹ * b) * G.weylPoint w ∈ G.borelPoints := by
    simpa only [mul_inv_rev, mul_assoc] using hB
  have he := G.eq_one_of_oppositeUnipotent_borel _ hU hB'
  have hconj := congrArg (fun z : G.points => G.weylPoint w * z * (G.weylPoint w)⁻¹) he
  have hg : (a : G.points)⁻¹ * b = 1 := by simpa [mul_assoc] using hconj
  exact Subtype.ext (inv_mul_eq_one.mp hg)

/-- An inversion-root flag belongs to its Schubert cell's Borel orbit. -/
theorem schubertPointMap_orbit (w : G.weylGroup) (u : schubertUnipotentPoints G w) :
    flagVarietyPointsEquiv G (schubertPointMap G w u) ∈
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w) := by
  apply (mem_schubertOrbit_iff G w _).mpr
  refine ⟨u, G.unipotent_le_borel (G.rootSubsetPoints_le_unipotent _ _ u.property),
    1, G.borelPoints.one_mem, ?_⟩
  group

/-- Every flag in a Schubert cell has inversion-root coordinates. -/
theorem exists_schubertPointMap (w : G.weylGroup) (q : flagPoints G)
    (hq : flagVarietyPointsEquiv G q ∈
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w)) :
    ∃ u : schubertUnipotentPoints G w, schubertPointMap G w u = q := by
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
  rw [weylFlagPoint, borelFlag_smul] at hb
  have hq' : flagProjection G ((GroupActions.borelPointsMulEquiv G b : G.points) *
      G.weylPoint w) = q := (flagVarietyPointsEquiv G).injective hb
  obtain ⟨u₁, hu₁, u₂, hu₂, t, ht, he⟩ := borelRootFactorization G w
    (GroupActions.borelPointsMulEquiv G b) (GroupActions.borelPointsMulEquiv G b).property
  refine ⟨⟨u₁, hu₁⟩, ?_⟩
  change flagProjection G (u₁ * G.weylPoint w) = q
  rw [← hq']
  apply (flagProjection_eq_iff G _ _).mpr
  have hU : (G.weylPoint w)⁻¹ * u₂ * G.weylPoint w ∈ G.borelPoints :=
    G.unipotent_le_borel (G.noninversionPoints_conj_unipotent w u₂ hu₂)
  have hT : (G.weylPoint w)⁻¹ * t * G.weylPoint w ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) t).mp ht
  rw [← he]
  convert G.borelPoints.mul_mem hU (G.torus_le_borel hT) using 1
  group

/-- Every rational flag has an inversion-root normal form for a Weyl element. -/
theorem flagPoint_normalForm (q : flagPoints G) :
    ∃ (w : G.weylGroup) (u : schubertUnipotentPoints G w), schubertPointMap G w u = q := by
  obtain ⟨w, hw⟩ := schubertOrbits_cover G (flagVarietyPointsEquiv G q)
  obtain ⟨u, hu⟩ := exists_schubertPointMap G w q hw
  exact ⟨w, u, hu⟩

/-- The inversion-root morphism has exactly the rational image of the Schubert cell. -/
theorem schubertRootMorphism_range (w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (schubertRootMorphism G w)) =
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) := by
  rw [schubertCell_points_range]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [schubertRootMorphism_points]
    exact schubertPointMap_orbit G w _
  · intro hx
    obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
    obtain ⟨u, hu⟩ := exists_schubertPointMap G w q hx
    refine ⟨(GroupActions.rootSubsetPointsMulEquiv G _
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).symm u, ?_⟩
    rw [schubertRootMorphism_points, MulEquiv.apply_symm_apply]
    exact congrArg (flagVarietyPointsEquiv G) hu

end
end SchubertGeometry
