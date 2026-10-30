import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.SchubertGeometry.Roots.Subgroups
import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.Paper.Deodhar.ComponentWeights

/-! # Standard forms and ordered root subgroups

The standard-form chart factors representatives and component flags into their ordered
root-subgroup images, with a puncture at every omitted position.
-/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry SchubertOrbits
open scoped Pointwise
namespace SchubertOrbits
noncomputable section
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- Selected factors are the canonical negative-root subgroup, punctured at omitted positions. -/
theorem deodharRootFactors
    (j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression}) :
    gaAffineGroupTangent (subwordRootMap G expression j) ≠ 0 ∧
    gaAffineGroupTangent (subwordRootMap G expression j) ∈
      G.rootWeightSpace (G.rootSystem.reflectionPerm
        (subwordRootIndex G.rootBase expression j.val)
        (subwordRootIndex G.rootBase expression j.val)) ∧
    (j.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression →
      deodharRootFactorSet G expression j =
        (rootSubgroupPoints G (G.rootSystem.reflectionPerm
          (subwordRootIndex G.rootBase expression j.val)
          (subwordRootIndex G.rootBase expression j.val)) : Set G.points) \ {1}) ∧
    (j.val ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
      deodharRootFactorSet G expression j =
        (rootSubgroupPoints G (G.rootSystem.reflectionPerm
          (subwordRootIndex G.rootBase expression j.val)
          (subwordRootIndex G.rootBase expression j.val)) : Set G.points)) := by
  have hmem : gaAffineGroupTangent (subwordRootMap G expression j) ∈
      G.rootWeightSpace (G.rootSystem.reflectionPerm
        (subwordRootIndex G.rootBase expression j.val)
        (subwordRootIndex G.rootBase expression j.val)) := by
    change gaAffineGroupTangent (subwordRootMap G expression j) ∈
      affineGroupCharacterWeightSpace G.torusSplit (subwordCharacter G expression j)
    exact subwordRootMap_tangent_mem G expression j
  have hrange := rootSubgroupPoints_eq_range G _ (subwordRootMap G expression j)
    hmem (subwordRootMap_tangent_ne_zero G expression j)
  refine ⟨subwordRootMap_tangent_ne_zero G expression j, hmem, ?_, ?_⟩
  · intro he
    have hs : {a : K | j.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression → a ≠ 0} =
        {a : K | a ≠ 0} := by ext a; simp only [he, true_implies]
    rw [deodharRootFactorSet, hs]
    exact rootSubgroupPoints_eq_puncture G _ (subwordRootMap G expression j)
      hmem (subwordRootMap_tangent_ne_zero G expression j)
  · intro hn
    have hne : j.val ∉ equalSteps (weylCoxeterSystem G.rootBase) expression :=
      fun he => hn.2 he.symm
    simpa only [deodharRootFactorSet, hne, false_implies, Set.ofPred_true, Set.image_univ]
      using hrange

variable (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

/-- The signed edge roots, their root subgroups, and the intrinsic standard-form coordinates. -/
theorem deodharRoot_definition :
    (∀ j : Fin word.length,
      j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression →
        subwordRoot (weylRealization G.rootBase) expression j =
          (weylRealization G.rootBase).action
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val)
            ((weylRealization G.rootBase).simpleRoot (word.get j)) ∧
        subwordRoot (weylRealization G.rootBase) expression j =
          edgeLabel (weylRealization G.rootBase)
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val)
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val *
              (weylCoxeterSystem G.rootBase).simple (word.get j))
            (((weylCoxeterSystem G.rootBase).isReflection_simple (word.get j)).conj
              (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val))) ∧
    (∀ j : Fin word.length,
      j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
        subwordRoot (weylRealization G.rootBase) expression j =
          -(weylRealization G.rootBase).action
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val)
            ((weylRealization G.rootBase).simpleRoot (word.get j)) ∧
        ∃ h : (bruhatGraph (weylCoxeterSystem G.rootBase)).Adj
            (expression.prefixProd (weylCoxeterSystem G.rootBase) (j.val + 1))
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val),
          subwordRoot (weylRealization G.rootBase) expression j =
            edgeLabel (weylRealization G.rootBase)
              (expression.prefixProd (weylCoxeterSystem G.rootBase) (j.val + 1))
              (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val) h) ∧
    (∀ j : Fin word.length,
      subwordRoot (weylRealization G.rootBase) expression j =
        normalizedRoot G.rootBase (subwordRootIndex G.rootBase expression j)) ∧
    (∀ j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (weylCoxeterSystem G.rootBase) expression},
      subwordRoot (weylRealization G.rootBase) expression j.val ∈
        (weylRealization G.rootBase).positiveRoots ∧
      ((weylRealization G.rootBase).rootReflection
        ⟨subwordRoot (weylRealization G.rootBase) expression j.val,
          subwordRoot_positive (weylRealization G.rootBase) expression hd j.val j.property⟩).val =
        expression.prefixProd (weylCoxeterSystem G.rootBase) j.val.val *
          (weylCoxeterSystem G.rootBase).simple (word.get j.val) *
            (expression.prefixProd (weylCoxeterSystem G.rootBase) j.val.val)⁻¹ ∧
      IsClosedImmersion (gaMorphism G (rootParameterMap G (G.rootSystem.reflectionPerm
        (subwordRootIndex G.rootBase expression j.val)
        (subwordRootIndex G.rootBase expression j.val)))).left ∧
      gaAffineGroupTangent (subwordRootMap G expression j) ≠ 0 ∧
      gaAffineGroupTangent (subwordRootMap G expression j) ∈
        G.rootWeightSpace (G.rootSystem.reflectionPerm
          (subwordRootIndex G.rootBase expression j.val)
          (subwordRootIndex G.rootBase expression j.val)) ∧
      (j.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression →
        deodharRootFactorSet G expression j =
          (rootSubgroupPoints G (G.rootSystem.reflectionPerm
            (subwordRootIndex G.rootBase expression j.val)
            (subwordRootIndex G.rootBase expression j.val)) : Set G.points) \ {1}) ∧
      (j.val ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
        deodharRootFactorSet G expression j =
          (rootSubgroupPoints G (G.rootSystem.reflectionPerm
            (subwordRootIndex G.rootBase expression j.val)
            (subwordRootIndex G.rootBase expression j.val)) : Set G.points))) ∧
    subwordWeightSpan (weylRealization G.rootBase) expression =
      Submodule.span ℝ ((subwordRoot (weylRealization G.rootBase) expression) ''
        (equalSteps (weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (weylCoxeterSystem G.rootBase) expression)) ∧
    subwordWeightDim (weylRealization G.rootBase) expression =
      Module.finrank ℝ (subwordWeightSpan (weylRealization G.rootBase) expression) ∧
    (deodharStandardFormMap G expression hred hd ≫ flagQuotientMorphism G =
      deodharInclusion G expression hred) ∧
    (∀ x : (deodharComponent G expression hred).points,
      mapPoints (deodharStandardFormMap G expression hred hd) x =
        reductivePointsEquiv G (subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (deodharParameterInclusion G expression)
              (mapPoints (deodharComponentIso G expression hred hd).inv x)) ⟨j⟩)
          word.length * subwordRepresentative G expression word.length)) ∧
    (∀ x : (deodharComponent G expression hred).points,
      x ∈ deodharGeneralPoints G expression hred hd ↔
        ∀ j : deodharIndex G expression,
          j.down.val ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (X := deodharParameters G expression)
              (Y := affineSpaceVariety K (deodharIndex G expression))
              (deodharParameterInclusion G expression)
              (mapPoints (X := deodharComponent G expression hred)
                (Y := deodharParameters G expression)
                (deodharComponentIso G expression hred hd).inv x)) j ≠ 0) := by
  refine ⟨?_, ?_, subwordRoot_eq_normalized G.rootBase expression, ?_, rfl, rfl,
    deodharStandardFormMap_quotient G expression hred hd,
    deodharStandardFormMap_rootProduct G expression hred hd, ?_⟩
  · intro j hj
    constructor
    · simpa only [List.get_eq_getElem] using
        subwordRoot_of_equal (weylRealization G.rootBase) expression j hj
    · simpa only [List.get_eq_getElem] using
        subwordRoot_eq_edgeLabel (weylRealization G.rootBase) expression hd j (Or.inl hj)
  · intro j hj
    constructor
    · simpa only [List.get_eq_getElem] using
        subwordRoot_of_negative (weylRealization G.rootBase) expression j hj
    · exact subwordRoot_negative_edge (weylRealization G.rootBase) expression hd j hj
  · intro j
    refine ⟨subwordRoot_positive (weylRealization G.rootBase) expression hd j.val j.property,
      ?_, rootParameterMorphism_isClosed G _, deodharRootFactors G expression j⟩
    simpa only [List.get_eq_getElem] using
      subwordRoot_reflection (weylRealization G.rootBase) expression hd j.val j.property
  · exact (deodharComponent_weights G expression hred hd).2.1

end
end SchubertOrbits
