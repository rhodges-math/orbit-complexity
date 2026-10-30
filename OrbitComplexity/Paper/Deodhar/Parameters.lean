import OrbitComplexity.GroupActions.Varieties.CoordinateOpens
import OrbitComplexity.Paper.Deodhar.WeightRank
import OrbitComplexity.GroupActions.Tori.WeightedAction
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import OrbitComplexity.GroupActions.Varieties.AffineDimension
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.SchubertGeometry.Deodhar.Parameters

/-! # Torus actions on independently constructed parameter varieties -/
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
open SchubertOrbits SchubertGeometry
noncomputable section
namespace SchubertOrbits

export SchubertGeometry (deodharIndex deodharParameterOpen
  deodharParameters deodharParameterInclusion
  deodharParameterInclusion_isOpen deodharParameter_points
  deodharParameters_irreducible deodharParameters_dim
  deodharIndex_card)
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

private def parameterWeights (j : deodharIndex G expression) : G.torusIndex →₀ ℤ :=
  (subwordCharacter G expression j.down).toAdd

set_option maxHeartbeats 400000 in
private theorem parameter_stable :
    letI := weightedAffineAction G (parameterWeights G expression)
    ∀ (t : (torusVariety G).points) (x : (deodharParameters G expression).points),
      t • mapPoints (deodharParameterInclusion G expression) x ∈
        Set.range (mapPoints (deodharParameterInclusion G expression)) := by
  let := weightedAffineAction G (parameterWeights G expression)
  intro t x
  have hx := (deodharParameter_points G expression).subset ⟨x, rfl⟩
  apply (deodharParameter_points G expression).symm.subset
  intro j hj
  exact (weightedAffineAction_ne_zero G (parameterWeights G expression) t _ j).mpr (hx j hj)

/-- The root characters define the diagonal torus action on the Deodhar parameter variety. -/
@[instance_reducible]
def deodharParameterAction :
    ModObj (torusVariety G).toOver (deodharParameters G expression).toOver := by
  letI := weightedAffineAction G (parameterWeights G expression)
  exact modObjOfInvariant (torusVariety G)
    (affineSpaceVariety K (deodharIndex G expression)) (deodharParameters G expression)
    (deodharParameterInclusion G expression) (parameter_stable G expression)

/-- The coordinate inclusion commutes with the diagonal torus actions. -/
theorem deodharParameterInclusion_isModHom :
    letI := weightedAffineAction G (parameterWeights G expression)
    letI := deodharParameterAction G expression
    IsModHom (torusVariety G).toOver (deodharParameterInclusion G expression) := by
  let := weightedAffineAction G (parameterWeights G expression)
  exact modObjOfInvariant_isModHom (torusVariety G)
    (affineSpaceVariety K (deodharIndex G expression)) (deodharParameters G expression)
    (deodharParameterInclusion G expression) (parameter_stable G expression)

/-- Every parameter coordinate scales by its negative signed-root character. -/
theorem deodharParameter_smul (t : (torusVariety G).points)
    (x : (deodharParameters G expression).points) (j : deodharIndex G expression) :
    letI := deodharParameterAction G expression
    affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
        (mapPoints (deodharParameterInclusion G expression) (t • x)) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
        (mapPoints (deodharParameterInclusion G expression) x) j *
          affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm
            (MonoidAlgebra.single (subwordCharacter G expression j.down) 1)) := by
  let := weightedAffineAction G (parameterWeights G expression)
  let := deodharParameterAction G expression
  have h := modObjOfInvariant_smul (torusVariety G)
    (affineSpaceVariety K (deodharIndex G expression)) (deodharParameters G expression)
    (deodharParameterInclusion G expression) (parameter_stable G expression) t x
  exact (congrArg (fun y => affineSpaceVarietyPointsEquiv K
    (deodharIndex G expression) y j) h).trans
      (weightedAffineAction_smul G (parameterWeights G expression) t _ j)

end SchubertOrbits
