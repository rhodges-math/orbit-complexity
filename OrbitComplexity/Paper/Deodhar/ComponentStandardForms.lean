import OrbitComplexity.SchubertGeometry.Deodhar.ComponentDecomposition
import OrbitComplexity.Paper.Deodhar.SubwordRootSubgroups
import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.SchubertGeometry.Deodhar.SubwordWeylPoints

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
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

private theorem form_point_factorization
    (y : (deodharStandardVariety G expression hred hd).points) :
    mapPoints (deodharStandardInclusion G expression hred hd) y =
      reductivePointsEquiv G (subwordRootProduct G expression
        (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
          (mapPoints (deodharParameterInclusion G expression)
            (mapPoints (deodharStandardParamIso G expression hred hd).inv y)) ⟨j⟩)
        word.length * subwordRepresentative G expression word.length) := by
  have hi : (deodharStandardParamIso G expression hred hd).inv ≫
      deodharPrefixLift G expression word.length =
        deodharStandardInclusion G expression hred hd := by
    rw [← deodharStandardParamIso_lift G expression hred hd, Iso.inv_hom_id_assoc]
  have hp := congrArg (fun f : (deodharStandardVariety G expression hred hd).toOver ⟶
    (reductiveVariety G).toOver => mapPoints (X := deodharStandardVariety G expression hred hd)
      (Y := reductiveVariety G) f y) hi.symm
  exact hp.trans ((mapPoints_comp (X := deodharStandardVariety G expression hred hd)
    (Y := deodharParameters G expression) (Z := reductiveVariety G)
    (deodharStandardParamIso G expression hred hd).inv
    (deodharPrefixLift G expression word.length) y).trans
      (deodharPrefixLift_points G expression word.length
        (mapPoints (deodharStandardParamIso G expression hred hd).inv y)))

/-- The signed subword product is the representative `u̇` of `u`, and standard representatives
and component flags have their ordered negative-root factors. -/
theorem deodharComponent_standardForm :
    subwordRepresentative G expression word.length =
      weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) ∧
    (deodharStandardFormMap G expression hred hd ≫ flagQuotientMorphism G =
      deodharInclusion G expression hred) ∧
    (∀ x : (deodharComponent G expression hred).points,
      mapPoints (deodharStandardFormMap G expression hred hd) x =
        reductivePointsEquiv G (subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (deodharParameterInclusion G expression)
              (mapPoints (deodharComponentIso G expression hred hd).inv x)) ⟨j⟩)
          word.length * subwordRepresentative G expression word.length)) ∧
    (∀ y : (deodharStandardVariety G expression hred hd).points,
      mapPoints (deodharStandardInclusion G expression hred hd) y =
        reductivePointsEquiv G (subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (deodharParameterInclusion G expression)
              (mapPoints (deodharStandardParamIso G expression hred hd).inv y)) ⟨j⟩)
          word.length * subwordRepresentative G expression word.length)) ∧
    (Set.range (fun x : (deodharStandardVariety G expression hred hd).points =>
      (reductivePointsEquiv G).symm
        (mapPoints (deodharStandardInclusion G expression hred hd) x)) =
      deodharRootProductSet G expression * {subwordRepresentative G expression word.length}) ∧
    (Set.range (mapPoints (deodharInclusion G expression hred)) =
      (fun g : G.points => flagVarietyPointsEquiv G (flagProjection G g)) ''
        (deodharRootProductSet G expression *
          {subwordRepresentative G expression word.length})) ∧
    ∀ j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (weylCoxeterSystem G.rootBase) expression},
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
          (subwordRootIndex G.rootBase expression j.val)) : Set G.points)) :=
  ⟨subwordRepresentative_eq_weylElement G expression word.length,
    deodharStandardFormMap_quotient G expression hred hd,
    deodharStandardFormMap_rootProduct G expression hred hd,
    form_point_factorization G expression hred hd,
    deodharStandard_products G expression hred hd,
    deodharComponent_products G hred expression hd, deodharRootFactors G expression⟩

end
end SchubertOrbits
