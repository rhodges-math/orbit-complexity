import OrbitComplexity.Paper.Deodhar.WeightRank
import OrbitComplexity.Paper.Deodhar.Representatives
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent
import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.SchubertGeometry.Deodhar.Representatives
import OrbitComplexity.SchubertGeometry.Deodhar.RootMaps

/-! # Root parameters of subexpressions

Conjugating the chosen simple-root parameters by signed prefix representatives gives root maps
at the omitted and decreasing positions. Their tangents have the negative signed-root characters,
and torus conjugation multiplies their parameters by the corresponding character values.

## Main definitions and results

* `SchubertGeometry.subwordRootMap`: the conjugated root map at a selected position.
* `SchubertGeometry.subwordRootMap_point`: its value as a conjugated Deodhar root element.
* `subwordRootMap_tangent_mem`: its root-character weight.
* `subwordRootMap_torus_points`: torus covariance on variety points.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Section 5.
-/

noncomputable section
namespace SchubertOrbits

export SchubertGeometry (subwordRootMap subwordRootMap_point
  subwordRootMap_tangent_ne_zero)
open BruhatIntervals ReductiveGroups TauCeti GroupActions AlgebraicGeometry
open SchubertOrbits SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem rootPerm_neg (w : G.weylGroup) (r : G.rootIndex) :
    G.rootSystem.weylGroupToPerm w (-r) = -G.rootSystem.weylGroupToPerm w r := by
  apply G.rootSystem.root.injective
  rw [← G.rootSystem.weylGroup_apply_root]
  change w • (-G.rootSystem.root r) = -G.rootSystem.root (G.rootSystem.weylGroupToPerm w r)
  rw [smul_neg, G.rootSystem.weylGroup_apply_root]

variable {word : List G.rootBase.support} (expression : Subexpression word)

private def sourceMap (j : Fin word.length) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K := by
  classical
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    G.simpleRootMap word[j.val] else G.negativeSimpleRootMap word[j.val]

private def sourceIndex (j : Fin word.length) : G.rootIndex := by
  classical
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    (word[j.val] : G.rootIndex) else -(word[j.val] : G.rootIndex)

private theorem rootMap_expansion
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) :
    SchubertGeometry.subwordRootMap G expression j =
      (sourceMap G expression j.val).comp
        (affineGroupConjugationBialgHom
          (SchubertGeometry.subwordRepresentative G expression j.val.val)) := rfl

private theorem sourceMap_tangent_mem (j : Fin word.length) :
    gaAffineGroupTangent (sourceMap G expression j) ∈
      G.rootWeightSpace (sourceIndex G expression j) := by
  classical
  unfold sourceMap sourceIndex
  split
  · exact G.simpleRootMap_tangent_mem _
  · exact G.negativeRootMap_tangent_mem _

private theorem sourceIndex_transport (j : Fin word.length) :
    G.rootSystem.weylGroupToPerm
        (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) j.val)
        (sourceIndex G expression j) =
      G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j)
        (subwordRootIndex G.rootBase expression j) := by
  classical
  by_cases hn : j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
  · simp only [sourceIndex, subwordRootIndex, hn, ↓reduceIte,
      LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg, neg_neg]
  · simp only [sourceIndex, subwordRootIndex, hn, ↓reduceIte,
      LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg]
    exact rootPerm_neg G _ _

set_option maxHeartbeats 400000 in
/-- The conjugated root tangent has the negative signed-root character of its selected position. -/
theorem subwordRootMap_tangent_mem
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) :
    gaAffineGroupTangent (SchubertGeometry.subwordRootMap G expression j) ∈
      affineGroupCharacterWeightSpace G.torusSplit (subwordCharacter G expression j) := by
  change gaAffineGroupTangent (SchubertGeometry.subwordRootMap G expression j) ∈
    G.rootWeightSpace (G.rootSystem.reflectionPerm
      (subwordRootIndex G.rootBase expression j.val)
      (subwordRootIndex G.rootBase expression j.val))
  rw [rootMap_expansion, gaTangent_comp_conjugation]
  have hmem : affineGroupAdjointLieEquiv (SchubertGeometry.subwordRepresentative G expression
    j.val.val)
      (gaAffineGroupTangent (sourceMap G expression j.val)) ∈
        (G.rootWeightSpace (sourceIndex G expression j.val)).map
          ((affineGroupAdjointLieEquiv
            (SchubertGeometry.subwordRepresentative G expression j.val.val)).toLinearEquiv :
            G.tangent →ₗ[K] G.tangent) :=
    Submodule.mem_map.mpr ⟨_, sourceMap_tangent_mem G expression j.val, rfl⟩
  rw [SchubertGeometry.subwordRepresentative_transport G expression j.val.val,
    sourceIndex_transport G expression j.val] at hmem
  exact hmem

/-- A split-torus point conjugates a selected root parameter by its negative-root character. -/
theorem subwordRootMap_torus_conj
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression})
    (t : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) (a : K) :
    AlgHom.mapDomain G.torusSplit t * gaParameterPoint (SchubertGeometry.subwordRootMap G
      expression j) a *
        (AlgHom.mapDomain G.torusSplit t)⁻¹ =
      gaParameterPoint (SchubertGeometry.subwordRootMap G expression j)
        (t.ofConv (MonoidAlgebra.single (subwordCharacter G expression j) 1) * a) :=
  GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit _ t _
    (subwordRootMap_tangent_mem G expression j) a

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

omit [IsAlgClosed K] [CharZero K] in
private theorem torusPoint_split (t : (torusVariety G).points) :
    (torusPointsMulEquiv G t : G.points) =
      AlgHom.mapDomain G.torusSplit (WithConv.toConv
        ((affinePointsEquiv.symm t).comp (torusCoordinateEquiv G).symm.toAlgHom)) := by
  rw [torusPointsMulEquiv_coe]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  change affinePointsEquiv.symm t (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
    affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm (G.torusSplit a))
  rw [← torusCoordinateEquiv_mk]
  exact congrArg (affinePointsEquiv.symm t) ((torusCoordinateEquiv G).symm_apply_apply _).symm

/-- On torus-variety points, conjugation rescales the root parameter by coordinate evaluation. -/
theorem subwordRootMap_torus_points
    (j : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression})
    (t : (torusVariety G).points) (a : K) :
    (torusPointsMulEquiv G t : G.points) * gaParameterPoint (SchubertGeometry.subwordRootMap G
      expression j) a *
        (torusPointsMulEquiv G t : G.points)⁻¹ =
      gaParameterPoint (SchubertGeometry.subwordRootMap G expression j)
        (affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm
          (MonoidAlgebra.single (subwordCharacter G expression j) 1)) * a) := by
  rw [torusPoint_split G t]
  exact subwordRootMap_torus_conj G expression j _ a

end SchubertOrbits
