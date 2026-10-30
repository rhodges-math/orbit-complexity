import OrbitComplexity.SchubertGeometry.Cells.Opposite

/-! # Richardson varieties and open Richardson strata

Reduced intersections of Schubert and opposite Schubert strata define Richardson varieties.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The closed support of a Richardson variety is the intersection of its two Schubert supports. -/
def richardsonSupport (v w : G.weylGroup) : Closeds (flagVariety G).scheme :=
  schubertSupport G w ⊓ oppositeSchubertSupport G v

/-- The Richardson variety is the reduced intersection of its Schubert varieties. -/
abbrev richardsonVariety (v w : G.weylGroup) : GroupActions.Variety K :=
  (flagVariety G).closedSubvariety (richardsonSupport G v w)

/-- The closed inclusion of a Richardson variety into the flag variety. -/
abbrev richardsonInclusion (v w : G.weylGroup) :
    (richardsonVariety G v w).toOver ⟶ (flagVariety G).toOver :=
  (flagVariety G).closedInclusion (richardsonSupport G v w)

/-- The Richardson inclusion has image the intersection of the two Schubert images. -/
theorem richardsonInclusion_range (v w : G.weylGroup) :
    Set.range (richardsonInclusion G v w).left =
      Set.range (schubertInclusion G w).left ∩
        Set.range (oppositeSchubertInclusion G v).left := by
  rw [GroupActions.Variety.closedInclusion_range, schubertInclusion_range,
    oppositeSchubertInclusion_range]
  rfl

/-- The open Richardson support is the intersection of the two Schubert cells. -/
def richardsonCellSupport (v w : G.weylGroup) : Set (flagVariety G).scheme :=
  Set.range (schubertCellInclusion G w).left ∩
    Set.range (oppositeSchubertCellInclusion G v).left

private theorem richardsonCell_locallyClosed (v w : G.weylGroup) :
    IsLocallyClosed (richardsonCellSupport G v w) := by
  change IsLocallyClosed (Set.range (schubertCellInclusion G w).left ∩
    Set.range (oppositeSchubertCellInclusion G v).left)
  rw [GroupActions.orbitInclusion_range, GroupActions.orbitInclusion_range]
  exact (GroupActions.orbitImage_locallyClosed _ _ _).inter
    (GroupActions.orbitImage_locallyClosed _ _ _)

/-- The open Richardson stratum carries the reduced induced locally closed structure. -/
abbrev richardsonCell (v w : G.weylGroup) : GroupActions.Variety K :=
  (flagVariety G).locallyClosedSubvariety (richardsonCellSupport G v w)
    (richardsonCell_locallyClosed G v w)

/-- The locally closed inclusion of the open Richardson stratum. -/
abbrev richardsonCellInclusion (v w : G.weylGroup) :
    (richardsonCell G v w).toOver ⟶ (flagVariety G).toOver :=
  (flagVariety G).locallyClosedInclusion (richardsonCellSupport G v w)
    (richardsonCell_locallyClosed G v w)

/-- The open Richardson stratum has exactly the intersection of the two cell images. -/
theorem richardsonCellInclusion_range (v w : G.weylGroup) :
    Set.range (richardsonCellInclusion G v w).left =
      Set.range (schubertCellInclusion G w).left ∩
        Set.range (oppositeSchubertCellInclusion G v).left :=
  GroupActions.Variety.locallyClosedInclusion_range _ _ _

end
end SchubertGeometry
