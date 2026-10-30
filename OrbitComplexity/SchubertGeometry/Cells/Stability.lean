import OrbitComplexity.SchubertGeometry.Cells.Richardson
import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import Batteries.Tactic.Lint

/-! # Stability of flag strata

Borel orbits are Borel stable, and the chosen torus acts through both Borel subgroups.
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The chosen torus acts algebraically on the flag variety. -/
instance flagTorusAction :
    ModObj (GroupActions.torusVariety G).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (GroupActions.torusInclusion G) (flagVariety G).toOver

/-- Torus multiplication on flag points is its ambient group action. -/
theorem torusFlag_smul (t : (GroupActions.torusVariety G).points) (x : flagPoints G) :
    t • flagVarietyPointsEquiv G x = flagVarietyPointsEquiv G
      ((GroupActions.torusPointsMulEquiv G t : G.points) • x) := by
  rw [GroupActions.Variety.restricted_smul (GroupActions.torusInclusion G),
    GroupActions.torusInclusion_points]
  exact flagVarietyAction_points G _ x

private theorem torus_weyl_point_fixed (w : G.weylGroup) (t : G.torusPoints) :
    (t : G.points) • flagProjection G (G.weylPoint w) =
      flagProjection G (G.weylPoint w) := by
  rw [← flagProjection_smul]
  apply (flagProjection_eq_iff G _ _).mpr
  have ht : (G.weylPoint w)⁻¹ * (t : G.points)⁻¹ * G.weylPoint w ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) _).mp
      (G.torusPoints.inv_mem t.property)
  simpa only [mul_inv_rev, mul_assoc] using G.torus_le_borel ht

private theorem schubertPointMap_torus_conj (w : G.weylGroup)
    (u : schubertUnipotentPoints G w) (t : G.torusPoints)
    (hc : (t : G.points) * u.val * (t : G.points)⁻¹ ∈ schubertUnipotentPoints G w) :
    schubertPointMap G w ⟨(t : G.points) * u.val * (t : G.points)⁻¹, hc⟩ =
      (t : G.points) • schubertPointMap G w u := by
  change flagProjection G (((t : G.points) * u.val * (t : G.points)⁻¹) * G.weylPoint w) =
    (t : G.points) • flagProjection G (u.val * G.weylPoint w)
  rw [flagProjection_smul, flagProjection_smul, mul_smul, mul_smul]
  exact congrArg (fun q => (t : G.points) • (u.val • q))
    (torus_weyl_point_fixed G w t⁻¹)

/-- The flags fixed by the maximal torus are exactly the Weyl flags. -/
theorem torus_fixed_iff_weylFlag (x : (flagVariety G).points) :
    (∀ t : (GroupActions.torusVariety G).points, t • x = x) ↔
      ∃ w : G.weylGroup, x = weylFlagPoint G w := by
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
    obtain ⟨w, u, huq⟩ := flagPoint_normalForm G q
    have hfu (t : G.torusPoints) : (t : G.points) * u.val * (t : G.points)⁻¹ = u.val := by
      have hmem := G.rootSubsetPoints_conjugate_mem
        (ReductiveGroups.leftRootInversionIndices G.rootBase w)
        (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
        t.val u.val t.property u.property
      have htq : (t : G.points) • q = q := by
        have htx := hx ((GroupActions.torusPointsMulEquiv G).symm t)
        rw [torusFlag_smul, MulEquiv.apply_symm_apply] at htx
        exact (flagVarietyPointsEquiv G).injective htx
      have hflags :=
        (schubertPointMap_torus_conj G w u t hmem).trans
          ((congrArg (fun q => (t : G.points) • q) huq).trans (htq.trans huq.symm))
      exact congrArg Subtype.val (schubertPointMap_injective G w hflags)
    have huone : u.val = 1 :=
      G.unipotent_eq_one_of_torus_conj u.val
        (G.rootSubsetPoints_le_unipotent
          (ReductiveGroups.leftRootInversionIndices G.rootBase w)
          (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) u.property)
        (fun t ht => hfu ⟨t, ht⟩)
    refine ⟨w, ?_⟩
    simpa only [schubertPointMap, huone, one_mul, weylFlagPoint] using
      congrArg (flagVarietyPointsEquiv G) huq.symm
  · rintro ⟨w, rfl⟩
    intro t
    rw [weylFlagPoint, torusFlag_smul]
    exact congrArg (flagVarietyPointsEquiv G)
      (torus_weyl_point_fixed G w (GroupActions.torusPointsMulEquiv G t))

/-- The image of a Schubert cell is stable under the Borel action. -/
theorem schubertCell_stable (w : G.weylGroup) (b : (GroupActions.borelVariety G).points)
    {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w))) :
    b • x ∈ Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) := by
  rw [schubertCell_points_range] at hx ⊢
  exact MulAction.mem_orbit_of_mem_orbit b hx

private theorem torus_smul_as_borel (t : (GroupActions.torusVariety G).points)
    (x : (flagVariety G).points) :
    t • x = (GroupActions.borelPointsMulEquiv G).symm
      ⟨GroupActions.torusPointsMulEquiv G t,
        G.torus_le_borel (GroupActions.torusPointsMulEquiv G t).property⟩ • x := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  rw [torusFlag_smul, borelFlag_smul, MulEquiv.apply_symm_apply]

/-- The image of a Schubert cell is stable under the torus action. -/
theorem schubertCell_torus_stable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) := by
  rw [torus_smul_as_borel]
  exact schubertCell_stable G w _ hx

private theorem torus_smul_as_opposite (t : (GroupActions.torusVariety G).points)
    (x : (flagVariety G).points) :
    t • x = (GroupActions.oppositeBorelPointsMulEquiv G).symm
      ⟨GroupActions.torusPointsMulEquiv G t,
        G.torus_le_oppositeBorel (GroupActions.torusPointsMulEquiv G t).property⟩ • x := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  rw [torusFlag_smul, oppositeBorelFlag_smul, MulEquiv.apply_symm_apply]

/-- The rational image of an opposite Schubert cell is its opposite Borel orbit. -/
theorem oppositeSchubertCell_points_range (w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w)) =
      MulAction.orbit (GroupActions.oppositeBorelVariety G).points (weylFlagPoint G w) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (GroupActions.orbitPointsEquiv (GroupActions.oppositeBorelVariety G) (flagVariety G)
      (weylFlagPoint G w) z).property
  · intro hp
    obtain ⟨z, hz⟩ := (GroupActions.orbitPointsEquiv (GroupActions.oppositeBorelVariety G)
      (flagVariety G) (weylFlagPoint G w)).surjective ⟨p, hp⟩
    exact ⟨z, congrArg Subtype.val hz⟩

/-- The image of an opposite Schubert cell is stable under the torus action. -/
theorem oppositeSchubertCell_torus_stable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints
      (oppositeSchubertCellInclusion G w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w)) := by
  rw [torus_smul_as_opposite]
  rw [oppositeSchubertCell_points_range] at hx ⊢
  exact MulAction.mem_orbit_of_mem_orbit _ hx

end
end SchubertGeometry
