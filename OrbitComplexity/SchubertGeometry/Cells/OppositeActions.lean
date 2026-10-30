import OrbitComplexity.SchubertGeometry.Cells.Actions

/-! # Algebraic actions on opposite Schubert strata

Opposite Borel and torus actions restrict to the opposite Schubert strata.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeCellStable (w : G.weylGroup)
    (b : (GroupActions.oppositeBorelVariety G).points)
    (y : (oppositeSchubertCell G w).points) :
    b • GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w)) := by
  rw [oppositeSchubertCell_points_range]
  exact MulAction.mem_orbit_of_mem_orbit b
    (GroupActions.orbitPointsEquiv _ _ (weylFlagPoint G w) y).property

private theorem oppositeVarietyStable (w : G.weylGroup)
    (b : (GroupActions.oppositeBorelVariety G).points)
    (y : (oppositeSchubertVariety G w).points) :
    b • GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w)) :=
  oppositeSchubertVariety_stable G w b ⟨y, rfl⟩

/-- The opposite Borel acts algebraically on each opposite Schubert cell. -/
instance oppositeCellBorelAction (w : G.weylGroup) :
    ModObj (GroupActions.oppositeBorelVariety G).toOver (oppositeSchubertCell G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.oppositeBorelVariety G) (flagVariety G)
    (oppositeSchubertCell G w) (oppositeSchubertCellInclusion G w) (oppositeCellStable G w)

/-- The opposite Schubert cell inclusion is opposite Borel equivariant. -/
instance oppositeCellBorelEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.oppositeBorelVariety G).toOver (oppositeSchubertCellInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (oppositeCellStable G w)

/-- The opposite Borel acts algebraically on each opposite Schubert variety. -/
instance oppositeSchubertBorelAction (w : G.weylGroup) :
    ModObj (GroupActions.oppositeBorelVariety G).toOver (oppositeSchubertVariety G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.oppositeBorelVariety G) (flagVariety G)
    (oppositeSchubertVariety G w) (oppositeSchubertInclusion G w) (oppositeVarietyStable G w)

/-- The opposite Schubert variety inclusion is opposite Borel equivariant. -/
instance oppositeSchubertBorelEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.oppositeBorelVariety G).toOver (oppositeSchubertInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (oppositeVarietyStable G w)

private theorem oppositeCellTorusStable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (y : (oppositeSchubertCell G w).points) :
    t • GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w)) :=
  oppositeSchubertCell_torus_stable G w t ⟨y, rfl⟩

private theorem oppositeVarietyTorusStable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (y : (oppositeSchubertVariety G w).points) :
    t • GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w)) :=
  oppositeSchubertVariety_torus_stable G w t ⟨y, rfl⟩

/-- The torus acts algebraically on each opposite Schubert cell. -/
instance oppositeCellTorusAction (w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (oppositeSchubertCell G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (oppositeSchubertCell G w) (oppositeSchubertCellInclusion G w) (oppositeCellTorusStable G w)

/-- The opposite Schubert cell inclusion is torus equivariant. -/
instance oppositeCellTorusEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (oppositeSchubertCellInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (oppositeCellTorusStable G w)

/-- The torus acts algebraically on each opposite Schubert variety. -/
instance oppositeSchubertTorusAction (w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (oppositeSchubertVariety G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (oppositeSchubertVariety G w) (oppositeSchubertInclusion G w) (oppositeVarietyTorusStable G w)

/-- The opposite Schubert variety inclusion is torus equivariant. -/
instance oppositeSchubertTorusEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (oppositeSchubertInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (oppositeVarietyTorusStable G w)

end
end SchubertGeometry
