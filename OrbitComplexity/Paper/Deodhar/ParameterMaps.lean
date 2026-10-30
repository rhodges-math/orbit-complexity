import OrbitComplexity.Paper.Deodhar.Parameters
import OrbitComplexity.Paper.Deodhar.ProductActions
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterMaps

/-! # Equivariance of independently constructed parameter-prefix maps -/
open CategoryTheory
noncomputable section
namespace SchubertOrbits

export SchubertGeometry (deodharPrefixMorphism deodharPrefixMorphism_points)
open GroupActions GroupActions.Variety ReductiveGroups BruhatIntervals SchubertGeometry
open SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- Every parameter-prefix morphism is equivariant for its root-character torus action. -/
theorem deodharPrefixMorphism_isModHom (n : ℕ) :
    letI := deodharParameterAction G expression
    IsModHom (torusVariety G).toOver (SchubertGeometry.deodharPrefixMorphism G expression n) := by
  let := weightedAffineAction G (fun j : SchubertGeometry.deodharIndex G expression =>
    (subwordCharacter G expression j.down).toAdd)
  let := deodharParameterAction G expression
  let : IsModHom (torusVariety G).toOver (SchubertGeometry.deodharParameterInclusion G
    expression) :=
    deodharParameterInclusion_isModHom G expression
  let : IsModHom (torusVariety G).toOver (SchubertGeometry.subwordFlagMorphism G expression n) :=
    subwordFlagMorphism_isModHom G expression n
  exact inferInstanceAs (IsModHom (torusVariety G).toOver
    (SchubertGeometry.deodharParameterInclusion G expression ≫
      SchubertGeometry.subwordFlagMorphism G expression n))

end SchubertOrbits
