import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.GroupActions.Varieties.ClosedPoints
import OrbitComplexity.GroupActions.Varieties.Images

/-! # The Schubert decomposition on scheme points

Constructibility extends rational-point coverage and disjointness to all scheme points.
-/

open AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem cellUnion_eq_univ :
    (⋃ w : G.weylGroup, Set.range (schubertCellInclusion G w).left) = Set.univ := by
  let := ReductiveGroups.weylGroup_finite G.rootBase
  have : JacobsonSpace (flagVariety G).toOver.left := by
    change JacobsonSpace (flagVariety G).scheme
    exact LocallyOfFiniteType.jacobsonSpace (flagVariety G).toSpec
  apply GroupActions.constructible_eq
    (IsConstructible.iUnion (fun w =>
      GroupActions.Variety.isConstructible_range (schubertCellInclusion G w))) .univ
  ext p
  constructor
  · rintro ⟨_, hp⟩
    exact ⟨Set.mem_univ p, hp⟩
  · rintro ⟨_, hp⟩
    have hp' : p ∈ Set.range (flagVariety G).pointMap := by
      rw [GroupActions.Variety.pointMap_range]
      exact hp
    obtain ⟨x, rfl⟩ := hp'
    obtain ⟨w, hw⟩ := schubertOrbits_cover G x
    rw [← schubertCell_points_range] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨Set.mem_iUnion.mpr ⟨w, ?_⟩, hp⟩
    refine ⟨(schubertCell G w).pointMap z, ?_⟩
    rw [← GroupActions.Variety.pointMap_mapPoints, hz]

/-- Every scheme point of the flag variety belongs to a Schubert cell. -/
theorem schubertCells_cover (x : (flagVariety G).scheme) :
    ∃ w : G.weylGroup, x ∈ Set.range (schubertCellInclusion G w).left := by
  apply Set.mem_iUnion.mp
  rw [cellUnion_eq_univ]
  exact Set.mem_univ x

/-- Two Schubert cells containing the same scheme point have equal Weyl indices. -/
theorem schubertCells_disjoint {v w : G.weylGroup} {x : (flagVariety G).scheme}
    (hv : x ∈ Set.range (schubertCellInclusion G v).left)
    (hw : x ∈ Set.range (schubertCellInclusion G w).left) : v = w := by
  have : JacobsonSpace (flagVariety G).toOver.left := by
    change JacobsonSpace (flagVariety G).scheme
    exact LocallyOfFiniteType.jacobsonSpace (flagVariety G).toSpec
  obtain ⟨p, hp, hclosed⟩ := GroupActions.constructible_closedPoint
    ((GroupActions.Variety.isConstructible_range (schubertCellInclusion G v)).inter
      (GroupActions.Variety.isConstructible_range (schubertCellInclusion G w))) ⟨x, hv, hw⟩
  have hp' : p ∈ Set.range (flagVariety G).pointMap := by
    rw [GroupActions.Variety.pointMap_range]
    exact hclosed
  obtain ⟨q, rfl⟩ := hp'
  obtain ⟨a, ha⟩ := GroupActions.Variety.exists_mapPoints_eq
    (schubertCellInclusion G v) q hp.1
  obtain ⟨b, hb⟩ := GroupActions.Variety.exists_mapPoints_eq
    (schubertCellInclusion G w) q hp.2
  apply schubertOrbits_disjoint G (x := q)
  · rw [← schubertCell_points_range]
    exact ⟨a, ha⟩
  · rw [← schubertCell_points_range]
    exact ⟨b, hb⟩

end
end SchubertGeometry
