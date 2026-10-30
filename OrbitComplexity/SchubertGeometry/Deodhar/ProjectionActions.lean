import OrbitComplexity.SchubertGeometry.Deodhar.PartialProjection
import OrbitComplexity.SchubertGeometry.Cells.ActionPoints
import OrbitComplexity.GroupActions.Actions.EquivariantPoints

/-! # Borel-equivariant cell projections

The preceding cell has at most one flag above each rank-one partial flag. Since left
multiplication preserves partial projection, the increasing-cell projection is Borel equivariant.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def cellFlag (w : G.weylGroup) (z : (schubertCell G w).points) : flagPoints G :=
  (flagVarietyPointsEquiv G).symm
    (GroupActions.Variety.mapPoints (schubertCellInclusion G w) z)

private theorem cellFlag_injective (w : G.weylGroup) : Function.Injective (cellFlag G w) :=
  (flagVarietyPointsEquiv G).symm.injective.comp
    (GroupActions.Variety.mapPoints_injective_of_mono (schubertCellInclusion G w))

private theorem cellFlag_mem (w : G.weylGroup) (z : (schubertCell G w).points) :
    flagVarietyPointsEquiv G (cellFlag G w z) ∈
      MulAction.orbit (GroupActions.borelVariety G).points (weylFlagPoint G w) := by
  rw [cellFlag, Equiv.apply_symm_apply, ← schubertCell_points_range]
  exact ⟨z, rfl⟩

private theorem cellFlag_smul (w : G.weylGroup)
    (b : (GroupActions.borelVariety G).points) (z : (schubertCell G w).points) :
    cellFlag G w (b • z) = (GroupActions.borelPointsMulEquiv G b : G.points) •
      cellFlag G w z := by
  apply (flagVarietyPointsEquiv G).injective
  rw [cellFlag, Equiv.apply_symm_apply]
  have h := borelFlag_smul G b (cellFlag G w z)
  rw [cellFlag, Equiv.apply_symm_apply] at h
  exact (schubertCell_smul G w b z).trans h

variable (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

/-- The increasing-cell projection commutes with the Borel action on rational points. -/
theorem rankOneProjection_smul (b : (GroupActions.borelVariety G).points)
    (z : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).points) :
    GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw) (b • z) =
      b • GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw) z := by
  let v := w * RootPairing.weylGroup.ofIdx G.rootSystem i
  let π := GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw)
  let g : G.points := GroupActions.borelPointsMulEquiv G b
  have hc (y : (schubertCell G v).points) :
      rankOnePartialProjection G i (cellFlag G v y) =
        rankOnePartialProjection G i (cellFlag G w (π y)) :=
    rankOnePartial_projection G w i hw y
  have hs (q : G.weylGroup) (y : (schubertCell G q).points) :
      rankOnePartialProjection G i (cellFlag G q (b • y)) =
        g • rankOnePartialProjection G i (cellFlag G q y) :=
    (congrArg (rankOnePartialProjection G i) (cellFlag_smul G q b y)).trans
      (rankOnePartial_smul G i g (cellFlag G q y))
  have he : rankOnePartialProjection G i (cellFlag G w (π (b • z))) =
      rankOnePartialProjection G i (cellFlag G w (b • π z)) :=
    (hc (b • z)).symm.trans ((hs v z).trans
      ((congrArg (fun q => g • q) (hc z)).trans (hs w (π z)).symm))
  apply cellFlag_injective G w
  exact rankOnePartial_injOn G w i hw (cellFlag_mem G w (π (b • z)))
    (cellFlag_mem G w (b • π z)) he

/-- The increasing-cell projection is equivariant for the algebraic Borel actions. -/
instance rankOneProjectionEquivariant :
    IsModHom (GroupActions.borelVariety G).toOver (rankOneCellProjection G w i hw) :=
  GroupActions.Variety.isModHom_of_points (GroupActions.borelVariety G) _ _ _
    (rankOneProjection_smul G w i hw)

end
end SchubertGeometry
