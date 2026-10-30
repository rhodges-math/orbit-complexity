import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties

/-! # Algebraic actions on Schubert strata

The invariant reduced strata inherit the Borel and torus actions from the flag variety.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem cellStable (w : G.weylGroup) (b : (GroupActions.borelVariety G).points)
    (y : (schubertCell G w).points) :
    b • GroupActions.Variety.mapPoints (schubertCellInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) :=
  schubertCell_stable G w b ⟨y, rfl⟩

private theorem varietyStable (w : G.weylGroup) (b : (GroupActions.borelVariety G).points)
    (y : (schubertVariety G w).points) :
    b • GroupActions.Variety.mapPoints (schubertInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w)) :=
  schubertVariety_stable G w b ⟨y, rfl⟩

/-- The Borel acts algebraically on each Schubert cell. -/
instance schubertCellBorelAction (w : G.weylGroup) :
    ModObj (GroupActions.borelVariety G).toOver (schubertCell G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.borelVariety G) (flagVariety G)
    (schubertCell G w) (schubertCellInclusion G w) (cellStable G w)

/-- The Schubert cell inclusion is Borel equivariant. -/
instance schubertCellBorelEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.borelVariety G).toOver (schubertCellInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (cellStable G w)

/-- The Borel acts algebraically on each Schubert variety. -/
instance schubertBorelAction (w : G.weylGroup) :
    ModObj (GroupActions.borelVariety G).toOver (schubertVariety G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.borelVariety G) (flagVariety G)
    (schubertVariety G w) (schubertInclusion G w) (varietyStable G w)

/-- The Schubert variety inclusion is Borel equivariant. -/
instance schubertBorelEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.borelVariety G).toOver (schubertInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (varietyStable G w)

private theorem cellTorusStable (w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (y : (schubertCell G w).points) :
    t • GroupActions.Variety.mapPoints (schubertCellInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) :=
  schubertCell_torus_stable G w t ⟨y, rfl⟩

private theorem varietyTorusStable (w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (y : (schubertVariety G w).points) :
    t • GroupActions.Variety.mapPoints (schubertInclusion G w) y ∈
      Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w)) :=
  schubertVariety_torus_stable G w t ⟨y, rfl⟩

/-- The torus acts algebraically on each Schubert cell. -/
instance schubertCellTorusAction (w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (schubertCell G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (schubertCell G w) (schubertCellInclusion G w) (cellTorusStable G w)

/-- The Schubert cell inclusion is torus equivariant. -/
instance schubertCellTorusEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (schubertCellInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (cellTorusStable G w)

/-- The torus acts algebraically on each Schubert variety. -/
instance schubertTorusAction (w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver (schubertVariety G w).toOver :=
  GroupActions.Variety.modObjOfInvariant (GroupActions.torusVariety G) (flagVariety G)
    (schubertVariety G w) (schubertInclusion G w) (varietyTorusStable G w)

/-- The Schubert variety inclusion is torus equivariant. -/
instance schubertTorusEquivariant (w : G.weylGroup) :
    IsModHom (GroupActions.torusVariety G).toOver (schubertInclusion G w) :=
  GroupActions.Variety.modObjOfInvariant_isModHom _ _ _ _ (varietyTorusStable G w)

end
end SchubertGeometry
