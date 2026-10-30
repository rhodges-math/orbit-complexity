import OrbitComplexity.SchubertGeometry.Cells.SchubertClosure
import OrbitComplexity.GroupActions.Varieties.OppositeBorelPoints

/-! # Opposite Schubert cells and varieties

Opposite Borel orbits and their reduced closures define the opposite Schubert strata.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The opposite Borel acts algebraically on the flag variety by left multiplication. -/
instance flagOppositeBorelAction :
    ModObj (GroupActions.oppositeBorelVariety G).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (GroupActions.oppositeBorelInclusion G) (flagVariety G).toOver

/-- The opposite Borel action is multiplication by its ambient group point. -/
theorem oppositeBorelFlag_smul (b : (GroupActions.oppositeBorelVariety G).points)
    (x : flagPoints G) :
    b • flagVarietyPointsEquiv G x = flagVarietyPointsEquiv G
      ((GroupActions.oppositeBorelPointsMulEquiv G b : G.points) • x) := by
  rw [GroupActions.Variety.restricted_smul (GroupActions.oppositeBorelInclusion G),
    GroupActions.oppositeBorelInclusion_points]
  exact flagVarietyAction_points G _ x

/-- The opposite Schubert cell is the opposite Borel orbit of its Weyl flag. -/
abbrev oppositeSchubertCell (w : G.weylGroup) : GroupActions.Variety K :=
  GroupActions.orbitVariety (GroupActions.oppositeBorelVariety G) (flagVariety G)
    (weylFlagPoint G w)

/-- The locally closed inclusion of an opposite Schubert cell. -/
abbrev oppositeSchubertCellInclusion (w : G.weylGroup) :
    (oppositeSchubertCell G w).toOver ⟶ (flagVariety G).toOver :=
  GroupActions.orbitInclusion (GroupActions.oppositeBorelVariety G) (flagVariety G)
    (weylFlagPoint G w)

/-- The closed support of an opposite Schubert variety is its orbit closure. -/
def oppositeSchubertSupport (w : G.weylGroup) : Closeds (flagVariety G).scheme :=
  ⟨closure (Set.range (oppositeSchubertCellInclusion G w).left), isClosed_closure⟩

/-- An opposite Schubert variety is the reduced closure of its opposite Borel orbit. -/
abbrev oppositeSchubertVariety (w : G.weylGroup) : GroupActions.Variety K :=
  (flagVariety G).closedSubvariety (oppositeSchubertSupport G w)

/-- The closed inclusion of an opposite Schubert variety. -/
abbrev oppositeSchubertInclusion (w : G.weylGroup) :
    (oppositeSchubertVariety G w).toOver ⟶ (flagVariety G).toOver :=
  (flagVariety G).closedInclusion (oppositeSchubertSupport G w)

/-- An opposite Schubert cell is integral. -/
instance oppositeSchubertCellIntegral (w : G.weylGroup) :
    IsIntegral (oppositeSchubertCell G w).scheme :=
  inferInstanceAs (IsIntegral (GroupActions.orbitVariety (GroupActions.oppositeBorelVariety G)
    (flagVariety G) (weylFlagPoint G w)).scheme)

/-- The opposite Schubert inclusion has image the closure of the opposite Schubert cell. -/
theorem oppositeSchubertInclusion_range (w : G.weylGroup) :
    Set.range (oppositeSchubertInclusion G w).left =
      closure (Set.range (oppositeSchubertCellInclusion G w).left) :=
  GroupActions.Variety.closedInclusion_range _ _

private def oppositeClosureHomeomorph (w : G.weylGroup) :
    (oppositeSchubertVariety G w).scheme ≃ₜ
      closure (Set.range (oppositeSchubertCellInclusion G w).left) :=
  (oppositeSchubertInclusion G w).left.isEmbedding.toHomeomorph.trans
    (.setCongr (oppositeSchubertInclusion_range G w))

/-- An opposite Schubert variety is irreducible. -/
instance oppositeSchubertIrreducible (w : G.weylGroup) :
    IrreducibleSpace (oppositeSchubertVariety G w).scheme := by
  have hr : IsIrreducible (Set.range (oppositeSchubertCellInclusion G w).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (oppositeSchubertCell G w).scheme).image
        (oppositeSchubertCellInclusion G w).left
        (oppositeSchubertCellInclusion G w).left.continuous.continuousOn
  have : IrreducibleSpace (closure (Set.range (oppositeSchubertCellInclusion G w).left)) :=
    isIrreducible_iff_irreducibleSpace.mp hr.closure
  exact (oppositeClosureHomeomorph G w).irreducibleSpace_iff.mpr inferInstance

/-- An opposite Schubert variety is integral. -/
instance oppositeSchubertVarietyIntegral (w : G.weylGroup) :
    IsIntegral (oppositeSchubertVariety G w).scheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end
end SchubertGeometry
