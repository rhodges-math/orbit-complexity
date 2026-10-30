import OrbitComplexity.SchubertGeometry.Deodhar.ParameterFrames
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Deodhar.ChartTransport
import OrbitComplexity.GroupActions.Varieties.ProductImmersions
import OrbitComplexity.GroupActions.Varieties.CoordinateInversion

/-! # Regular maps for one parameter step

The additive relative cell map restricts to the zero coordinate at an increasing step,
to every coordinate at a decreasing step, and to the reciprocal nonzero coordinate at an
omitted step.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private def additiveZeroMap {K : Type u} [Field K] (X : Variety K) :
    X.toOver ⟶ (additiveVariety K).toOver :=
  toUnit X.toOver ≫ (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : Fin word.length)
  (f : (deodharParameters G (expression.take n.val)).toOver ⟶
    (schubertCell G (simpleWeylWord G.rootBase (word.take n.val))).toOver)
  (hf : f ≫ schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n.val)) =
    deodharPrefixMorphism G (expression.take n.val) n.val)

include hf in
private theorem frame_projects :
    deodharPrefixLift G (expression.take n.val) n.val ≫ flagQuotientMorphism G =
      f ≫ schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n.val)) :=
  (deodharPrefixLift_projection G (expression.take n.val) n.val).trans hf.symm

/-- The regular prefix group lift gives the additive map in the next ordinary cell. -/
@[irreducible] def deodharFibreMap :
    (deodharParameters G (expression.take n.val)).toOver ⊗ (additiveVariety K).toOver ⟶
      (wordCell G word (n.val + 1)).toOver :=
  (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n.val)) (word.get n)
    (wordCell_ascent G word hred n.val n.isLt) (deodharParameters G (expression.take n.val))
    f (deodharPrefixLift G (expression.take n.val) n.val)
    (frame_projects G expression n f hf)).hom ≫
      pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n.val)) (word.get n)
        (wordCell_ascent G word hred n.val n.isLt)) ≫
          (wordCellExtensionIso G word n.val n.isLt).hom

/-- An increasing parameter step uses the zero section of the additive relative map. -/
@[irreducible] def deodharPositiveStepMap
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (wordCell G word (n.val + 1)).toOver :=
  (deodharPositiveStepIso G expression n hn).hom ≫
    lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
      (additiveZeroMap (deodharParameters G (expression.take n.val))) ≫
        deodharFibreMap G expression hred n f hf

/-- A decreasing parameter step uses the whole additive relative map. -/
@[irreducible] def deodharNegativeStepMap
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (wordCell G word (n.val + 1)).toOver :=
  (deodharNegativeStepIso G expression n hn).hom ≫
    deodharFibreMap G expression hred n f hf

/-- An omitted parameter step uses the reciprocal coordinate on the punctured additive factor. -/
@[irreducible] def deodharEqualStepMap
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (wordCell G word (n.val + 1)).toOver :=
  (deodharEqualStepIso G expression n hn).hom ≫
    (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
      ((puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K))) ≫
      deodharFibreMap G expression hred n f hf

end
end SchubertGeometry
