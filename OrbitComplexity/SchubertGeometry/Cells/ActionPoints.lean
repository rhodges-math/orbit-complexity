import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions

/-! # Point formulas for actions on flag strata

The inherited algebraic actions agree with the ambient action after inclusion in the flag variety.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The Borel action on cell points commutes with inclusion in the flag variety. -/
theorem schubertCell_smul (w : G.weylGroup) (b : (GroupActions.borelVariety G).points)
    (x : (schubertCell G w).points) :
    GroupActions.Variety.mapPoints (schubertCellInclusion G w) (b • x) =
      b • GroupActions.Variety.mapPoints (schubertCellInclusion G w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (schubertCellInclusion G w)
    (fun h y => schubertCell_stable G w h ⟨y, rfl⟩) b x

/-- The torus action on Schubert cell points commutes with the cell inclusion. -/
theorem schubertCell_torus_smul (w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (x : (schubertCell G w).points) :
    GroupActions.Variety.mapPoints (schubertCellInclusion G w) (t • x) =
      t • GroupActions.Variety.mapPoints (schubertCellInclusion G w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (schubertCellInclusion G w)
    (fun h y => schubertCell_torus_stable G w h ⟨y, rfl⟩) t x

/-- The torus action on Schubert variety points commutes with the closed inclusion. -/
theorem schubert_torus_smul (w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (x : (schubertVariety G w).points) :
    GroupActions.Variety.mapPoints (schubertInclusion G w) (t • x) =
      t • GroupActions.Variety.mapPoints (schubertInclusion G w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (schubertInclusion G w)
    (fun h y => schubertVariety_torus_stable G w h ⟨y, rfl⟩) t x

/-- The torus action on opposite cell points commutes with inclusion. -/
theorem oppositeCell_torus_smul (w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (x : (oppositeSchubertCell G w).points) :
    GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w) (t • x) =
      t • GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (oppositeSchubertCellInclusion G w)
    (fun h y => oppositeSchubertCell_torus_stable G w h ⟨y, rfl⟩) t x

/-- The torus action on opposite Schubert points commutes with the closed inclusion. -/
theorem oppositeSchubert_torus_smul (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (x : (oppositeSchubertVariety G w).points) :
    GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w) (t • x) =
      t • GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (oppositeSchubertInclusion G w)
    (fun h y => oppositeSchubertVariety_torus_stable G w h ⟨y, rfl⟩) t x

/-- The torus action on Richardson points commutes with the closed inclusion. -/
theorem richardson_torus_smul (v w : G.weylGroup) (t : (GroupActions.torusVariety G).points)
    (x : (richardsonVariety G v w).points) :
    GroupActions.Variety.mapPoints (richardsonInclusion G v w) (t • x) =
      t • GroupActions.Variety.mapPoints (richardsonInclusion G v w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (richardsonInclusion G v w)
    (fun h y => richardsonVariety_torus_stable G v w h ⟨y, rfl⟩) t x

/-- The torus action on open Richardson points commutes with inclusion. -/
theorem richardsonCell_torus_smul (v w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) (x : (richardsonCell G v w).points) :
    GroupActions.Variety.mapPoints (richardsonCellInclusion G v w) (t • x) =
      t • GroupActions.Variety.mapPoints (richardsonCellInclusion G v w) x :=
  GroupActions.Variety.modObjOfInvariant_smul _ _ _ (richardsonCellInclusion G v w)
    (fun h y => richardsonCell_torus_stable G v w h ⟨y, rfl⟩) t x

end
end SchubertGeometry
