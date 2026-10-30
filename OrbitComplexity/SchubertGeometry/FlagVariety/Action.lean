import OrbitComplexity.SchubertGeometry.FlagVariety.ActionMorphism
import OrbitComplexity.GroupActions.Actions.FromPoints

/-! # The algebraic action on the flag variety

The glued multiplication morphism satisfies the unit and associativity laws.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

@[instance_reducible] private def cosetPointAction :
    MulAction (GroupActions.reductiveVariety G).points
    (flagVariety G).points := by
  let : MulAction (GroupActions.reductiveVariety G).points (flagPoints G) :=
    MulAction.compHom _ (GroupActions.reductivePointsMulEquiv G).symm.toMonoidHom
  exact (flagVarietyPointsEquiv G).symm.mulAction (GroupActions.reductiveVariety G).points

/-- The reductive group acts algebraically on its flag variety by left multiplication. -/
instance flagVarietyAction :
    ModObj (GroupActions.reductiveVariety G).toOver (flagVariety G).toOver := by
  let := cosetPointAction G
  apply GroupActions.Variety.modObjOfPoints (GroupActions.reductiveVariety G)
    (flagVariety G) (flagActionMorphism G)
  intro h x
  exact flagActionMorphism_pair G h x

/-- The algebraic flag action induces the standard left action on Borel cosets. -/
theorem flagVarietyAction_points (g : G.points) (x : flagPoints G) :
    GroupActions.reductivePointsMulEquiv G g • flagVarietyPointsEquiv G x =
      flagVarietyPointsEquiv G (g • x) := by
  apply (flagVariety G).pointsEquivOverHom.injective
  rw [GroupActions.Variety.pointsEquivOverHom_smul]
  change lift ((GroupActions.reductiveVariety G).pointsEquivOverHom
      (GroupActions.reductivePointsMulEquiv G g))
      ((flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G x)) ≫
      flagActionMorphism G = _
  rw [flagActionMorphism_pair]
  simp only [MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]

end
end SchubertGeometry
