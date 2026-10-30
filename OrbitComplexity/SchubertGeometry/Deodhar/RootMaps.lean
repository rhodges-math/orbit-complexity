import OrbitComplexity.SchubertGeometry.Deodhar.Elements
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent

/-! # Root parameters of subexpressions

Conjugating the fixed simple-root parameters by signed prefix representatives gives the root
maps at omitted and decreasing positions. These maps have nonzero tangent vectors.
-/

noncomputable section
namespace SchubertGeometry
open BruhatIntervals ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

variable {word : List G.rootBase.support} (expression : Subexpression word)

private def sourceMap (j : Fin word.length) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K := by
  classical
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    G.simpleRootMap word[j.val] else G.negativeSimpleRootMap word[j.val]

/-- The simple-root parameter at a selected position, conjugated by its preceding representative. -/
def subwordRootMap (j : {position : Fin word.length //
    position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (sourceMap G expression j.val).comp
    (affineGroupConjugationBialgHom (subwordRepresentative G expression j.val.val))

/-- A selected root-map value is the conjugate of the corresponding Deodhar root element. -/
theorem subwordRootMap_point (parameters : Fin word.length → K)
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) :
    gaParameterPoint (subwordRootMap G expression j) (parameters j.val) =
      subwordRepresentative G expression j.val.val *
        deodharRootElement G expression parameters j.val *
        (subwordRepresentative G expression j.val.val)⁻¹ := by
  classical
  have hsource : gaParameterPoint (sourceMap G expression j.val) (parameters j.val) =
      deodharRootElement G expression parameters j.val := by
    unfold sourceMap deodharRootElement
    by_cases hn : j.val ∈ negativeSteps
        (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
    · simp only [hn, ↓reduceIte]
    · have he := j.property.resolve_right hn
      simp only [hn, he, ↓reduceIte]
  exact (gaPoints_comp_conjugation (sourceMap G expression j.val)
    (subwordRepresentative G expression j.val.val) (Multiplicative.ofAdd (parameters j.val))).trans
      (congrArg (fun x => subwordRepresentative G expression j.val.val * x *
        (subwordRepresentative G expression j.val.val)⁻¹) hsource)

private theorem sourceMap_tangent_ne_zero (j : Fin word.length) :
    gaAffineGroupTangent (sourceMap G expression j) ≠ 0 := by
  classical
  unfold sourceMap
  split
  · exact G.simpleRootMap_tangent_ne_zero _
  · exact G.negativeRootMap_tangent_ne_zero _

/-- Every selected conjugated root parameter has nonzero tangent. -/
theorem subwordRootMap_tangent_ne_zero
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) :
    gaAffineGroupTangent (subwordRootMap G expression j) ≠ 0 := by
  rw [subwordRootMap, gaTangent_comp_conjugation]
  intro hzero
  apply sourceMap_tangent_ne_zero G expression j.val
  exact (affineGroupAdjointLieEquiv _).injective (hzero.trans (map_zero _).symm)

end SchubertGeometry
