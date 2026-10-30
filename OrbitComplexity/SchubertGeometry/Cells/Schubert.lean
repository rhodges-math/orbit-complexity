import OrbitComplexity.SchubertGeometry.FlagVariety.BorelStabilizer
import OrbitComplexity.GroupActions.Actions.Restriction
import OrbitComplexity.GroupActions.Actions.OrbitVariety

/-! # Schubert cells and varieties

Borel orbits of Weyl flags carry their reduced locally closed scheme structures.
Their closures carry reduced closed subvariety structures.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The flag represented by a chosen Weyl group representative. -/
def weylFlagPoint (w : G.weylGroup) : (flagVariety G).points :=
  flagVarietyPointsEquiv G (flagProjection G (G.weylPoint w))

/-- The Borel acts algebraically on the flag variety by left multiplication. -/
instance flagBorelAction :
    ModObj (GroupActions.borelVariety G).toOver (flagVariety G).toOver :=
  Mod.scalarRestriction (GroupActions.borelInclusion G) (flagVariety G).toOver

/-- The Borel action on flag points is multiplication by its ambient group point. -/
theorem borelFlag_smul (b : (GroupActions.borelVariety G).points) (x : flagPoints G) :
    b • flagVarietyPointsEquiv G x = flagVarietyPointsEquiv G
      ((GroupActions.borelPointsMulEquiv G b : G.points) • x) := by
  rw [GroupActions.Variety.restricted_smul (GroupActions.borelInclusion G),
    GroupActions.borelInclusion_points]
  exact flagVarietyAction_points G _ x

/-- The Schubert cell is the Borel orbit of its Weyl flag with reduced induced structure. -/
abbrev schubertCell (w : G.weylGroup) : GroupActions.Variety K :=
  GroupActions.orbitVariety (GroupActions.borelVariety G) (flagVariety G) (weylFlagPoint G w)

/-- The locally closed inclusion of a Schubert cell in the flag variety. -/
abbrev schubertCellInclusion (w : G.weylGroup) :
    (schubertCell G w).toOver ⟶ (flagVariety G).toOver :=
  GroupActions.orbitInclusion (GroupActions.borelVariety G) (flagVariety G) (weylFlagPoint G w)

/-- The closed support of a Schubert variety is the closure of its cell. -/
def schubertSupport (w : G.weylGroup) : Closeds (flagVariety G).scheme :=
  ⟨closure (Set.range (schubertCellInclusion G w).left), isClosed_closure⟩

/-- The Schubert variety is the reduced closure of its Borel orbit. -/
abbrev schubertVariety (w : G.weylGroup) : GroupActions.Variety K :=
  (flagVariety G).closedSubvariety (schubertSupport G w)

/-- The closed inclusion of a Schubert variety in the flag variety. -/
abbrev schubertInclusion (w : G.weylGroup) :
    (schubertVariety G w).toOver ⟶ (flagVariety G).toOver :=
  (flagVariety G).closedInclusion (schubertSupport G w)

/-- A Schubert cell is an integral variety. -/
instance schubertCellIntegral (w : G.weylGroup) : IsIntegral (schubertCell G w).scheme :=
  inferInstanceAs (IsIntegral (GroupActions.orbitVariety (GroupActions.borelVariety G)
    (flagVariety G) (weylFlagPoint G w)).scheme)

/-- The image of a Schubert variety is the closure of its Schubert cell. -/
theorem schubertInclusion_range (w : G.weylGroup) :
    Set.range (schubertInclusion G w).left =
      closure (Set.range (schubertCellInclusion G w).left) :=
  GroupActions.Variety.closedInclusion_range _ _

end
end SchubertGeometry
