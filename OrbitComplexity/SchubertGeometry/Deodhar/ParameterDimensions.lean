import OrbitComplexity.SchubertGeometry.Deodhar.Parameters
import OrbitComplexity.BruhatIntervals.Words.StepCount
import Mathlib.Tactic

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups BruhatIntervals
/-! # Dimensions of Deodhar parameter varieties

The general step-count identity bounds the number of selected coordinates. When no step
is decreasing, that count equals the difference of word length and final Coxeter length.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support} (expression : Subexpression word)

/-- The parameter dimension is at most the word length minus the final Coxeter length. -/
theorem deodharParameters_dim_le :
    (deodharParameters G expression).dim ≤
      ((word.length - (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) : ℕ) :
          WithBot ℕ∞) := by
  have hc := subexpression_step_count (weylCoxeterSystem G.rootBase) expression
  have hi := deodharIndex_card G expression
  have hn : Nat.card (deodharIndex G expression) ≤ word.length -
      (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) := by
    omega
  rw [deodharParameters_dim]
  exact_mod_cast hn

/-- Positive parameters have dimension equal to the difference of endpoint lengths. -/
theorem positiveParameters_dim
    (hp : IsPositive (weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G expression).dim =
      ((word.length - (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) : ℕ) :
          WithBot ℕ∞) := by
  have hc := subexpression_step_count (weylCoxeterSystem G.rootBase) expression
  have hn := (isPositive_iff_negativeSteps_empty
    (weylCoxeterSystem G.rootBase) expression).mp hp
  rw [hn, Set.ncard_empty, mul_zero, add_zero] at hc
  have hi := deodharIndex_card G expression
  rw [hn, Set.ncard_empty, add_zero] at hi
  have he : Nat.card (deodharIndex G expression) = word.length -
      (weylCoxeterSystem G.rootBase).length
        (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length) := by
    omega
  exact (deodharParameters_dim G expression).trans
    (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) he)

end
end SchubertGeometry
