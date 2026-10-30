import OrbitComplexity.SchubertGeometry.Deodhar.ParameterDimensions
import OrbitComplexity.Paper.Deodhar.ParameterComplexity
import OrbitComplexity.Paper.Deodhar.Spans

/-! # Dimensions of positive Deodhar parameters

The general step-count and geometric dimension formulas are provided by the libraries.
The positive distinguished weight identity computes parameter complexity.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertOrbits

export BruhatIntervals (subexpression_step_count)
export SchubertGeometry (positiveParameters_dim)

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem positive_index_card
    (hp : IsPositive (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    Nat.card (deodharIndex G expression) = word.length -
      (ReductiveGroups.weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) word.length) := by
  have hc := subexpression_step_count (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
  have hn := (isPositive_iff_negativeSteps_empty
    (ReductiveGroups.weylCoxeterSystem G.rootBase) expression).mp hp
  rw [hn, Set.ncard_empty, mul_zero, add_zero] at hc
  have hi := deodharIndex_card G expression
  rw [hn, Set.ncard_empty, add_zero] at hi
  omega

/-- Positive distinguished parameters have endpoint length difference minus interval weight rank
as their torus complexity. -/
theorem positiveParameter_complexity
    (hred : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (hp : IsPositive (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    letI := deodharParameterAction G expression
    torusComplexity G (deodharParameters G expression) =
      word.length - (ReductiveGroups.weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) word.length) -
          algebraicDim (weylRealization G.rootBase)
            (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) word.length)
            ((ReductiveGroups.weylCoxeterSystem G.rootBase).wordProd word) := by
  have hs := (subwordWeightSpan_interval (weylRealization G.rootBase)
    expression hred hd).2 hp
  have hr := congrArg
    (fun V : Submodule ℝ (G.rootBase.support →₀ ℝ) => Module.finrank ℝ V) hs
  let := deodharParameterAction G expression
  rw [deodharParameter_complexity, positive_index_card G expression hp]
  exact congrArg (fun n => word.length -
    (ReductiveGroups.weylCoxeterSystem G.rootBase).length
      (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) word.length) - n) hr

end SchubertOrbits
