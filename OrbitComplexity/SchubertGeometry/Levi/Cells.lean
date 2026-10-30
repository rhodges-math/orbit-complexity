import OrbitComplexity.SchubertGeometry.Levi.Actions
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties

/-!
# Levi--Borel actions on Schubert cells

The intersection subgroup acts through the Borel on each Schubert cell. Its
restricted algebraic action makes the cell inclusion equivariant.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem leviBorel_smul_as_borel (I : Set G.rootBase.support)
    (b : (leviBorelVariety G I).points) (q : (flagVariety G).points) :
    b • q = (borelPointsMulEquiv G).symm
      ⟨leviBorelPointsMulEquiv G I b, (leviBorelPointsMulEquiv G I b).property.2⟩ • q := by
  obtain ⟨f, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
  rw [leviBorelFlag_smul, flagVarietyAction_points, borelFlag_smul,
    MulEquiv.apply_symm_apply]

/-- Every Schubert cell is stable under the standard Levi--Borel group. -/
theorem leviBorel_cell_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (b : (leviBorelVariety G I).points) {q : (flagVariety G).points}
    (hq : q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G w))) :
    b • q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G w)) := by
  rw [leviBorel_smul_as_borel]
  exact schubertCell_stable G w _ hq

/-- The Levi--Borel flag action restricts algebraically to every Schubert cell. -/
instance leviBorelCellAction (I : Set G.rootBase.support) (w : G.weylGroup) :
    ModObj (leviBorelVariety G I).toOver (schubertCell G w).toOver :=
  Variety.modObjOfInvariant (leviBorelVariety G I) (flagVariety G) (schubertCell G w)
    (schubertCellInclusion G w) (fun b x => leviBorel_cell_stable G I w b ⟨x, rfl⟩)

/-- The Schubert-cell inclusion is equivariant for the Levi--Borel actions. -/
instance leviBorelCellEquivariant (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (leviBorelVariety G I).toOver (schubertCellInclusion G w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ _

/-- The Levi--Borel action on a Schubert cell is its ambient flag action. -/
theorem leviBorelCell_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (b : (leviBorelVariety G I).points) (q : (schubertCell G w).points) :
    Variety.mapPoints (schubertCellInclusion G w) (b • q) =
      b • Variety.mapPoints (schubertCellInclusion G w) q :=
  Variety.modObjOfInvariant_smul _ _ _ _ _ b q

end SchubertGeometry
