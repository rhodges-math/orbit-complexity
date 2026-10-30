import OrbitComplexity.SchubertGeometry.Cells.OppositeActions

/-! # Torus actions on Richardson strata

The torus preserves both Schubert factors and hence acts on their reduced intersections.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem richardsonStable (v w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (y : (richardsonVariety G v w).points) :
    t • GroupActions.Variety.mapPoints (richardsonInclusion G v w) y ∈
      Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G v w)) :=
  richardsonVariety_torus_stable G v w t ⟨y, rfl⟩

/-- The torus acts algebraically on each Richardson variety. -/
instance richardsonTorusAction (v w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (richardsonVariety G v w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (richardsonVariety G v w) (richardsonInclusion G v w) (richardsonStable G v w)

/-- The Richardson inclusion is torus equivariant. -/
instance richardsonTorusEquivariant (v w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (richardsonInclusion G v w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (richardsonStable G v w)

private theorem richardsonCellStable (v w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (y : (richardsonCell G v w).points) :
    t • GroupActions.Variety.mapPoints (richardsonCellInclusion G v w) y ∈
      Set.range (GroupActions.Variety.mapPoints (richardsonCellInclusion G v w)) :=
  richardsonCell_torus_stable G v w t ⟨y, rfl⟩

/-- The torus acts algebraically on each open Richardson stratum. -/
instance richardsonCellTorusAction (v w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (richardsonCell G v w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (richardsonCell G v w) (richardsonCellInclusion G v w) (richardsonCellStable G v w)

/-- The open Richardson inclusion is torus equivariant. -/
instance richardsonCellTorusEquivariant (v w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (richardsonCellInclusion G v w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (richardsonCellStable G v w)

end
end SchubertGeometry
