import OrbitComplexity.Paper.Deodhar.Spans
import OrbitComplexity.BruhatIntervals.Words.Positive

/-!
# Attainment of the interval weight dimension

The unique positive distinguished subexpression of a fixed reduced word has the entire interval
label span. Every distinguished subexpression has its span inside that space, so its dimension
is bounded by the dimension attained by the positive distinguished subexpression.

## Main results

* `positive_subwordWeightSpan`: the unique positive distinguished expression attains the span.
* `subwordWeightDim_maximum`: the interval dimension is the attained maximum weight dimension.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Representation Theory 8 (2004),
  Section 3.
* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  Theorem 1.4.
-/

namespace SchubertOrbits

open BruhatIntervals

universe u v w

variable {Index : Type u} {W : Type v} {V : Type w} [Group W]
  {matrix : CoxeterMatrix Index} {cs : CoxeterSystem matrix W}
  [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))

/-- The unique positive distinguished subexpression has the complete interval label span
and hence the interval's algebraic dimension. -/
theorem positive_subwordWeightSpan {word : List Index} (hred : cs.IsReduced word)
    (u : W) (hle : cs.BruhatLE u (cs.wordProd word)) :
    ∃! expression : Subexpression word,
      expression.prefixProd cs word.length = u ∧ IsDistinguished cs expression ∧
      IsPositive cs expression ∧
      subwordWeightSpan realization expression = labelSpan realization u (cs.wordProd word) ∧
      subwordWeightDim realization expression = algebraicDim realization u (cs.wordProd word) := by
  obtain ⟨expression, hspec, hunique⟩ := positive_subexpression_unique cs hred u hle
  have hspan := (subwordWeightSpan_interval realization expression hred hspec.2.1).2 hspec.2.2
  rw [hspec.1] at hspan
  refine ⟨expression, ⟨hspec.1, hspec.2.1, hspec.2.2, hspan, ?_⟩, ?_⟩
  · exact congrArg (fun plane : Submodule ℝ V => Module.finrank ℝ plane) hspan
  · intro other hother
    exact hunique other ⟨hother.1, hother.2.1, hother.2.2.1⟩

/-- The algebraic dimension of an interval is the attained maximum of the weight dimensions
of all distinguished subexpressions with its lower endpoint. -/
theorem subwordWeightDim_maximum {word : List Index} (hred : cs.IsReduced word)
    (u : W) (hle : cs.BruhatLE u (cs.wordProd word)) :
    IsGreatest {dimension : ℕ | ∃ expression : Subexpression word,
      expression.prefixProd cs word.length = u ∧ IsDistinguished cs expression ∧
        subwordWeightDim realization expression = dimension}
      (algebraicDim realization u (cs.wordProd word)) := by
  obtain ⟨expression, hspec, _⟩ := positive_subwordWeightSpan realization hred u hle
  refine ⟨⟨expression, hspec.1, hspec.2.1, hspec.2.2.2.2⟩, ?_⟩
  rintro dimension ⟨other, hfinal, hdistinguished, rfl⟩
  have hspan := (subwordWeightSpan_interval realization other hred hdistinguished).1
  rw [hfinal] at hspan
  exact Submodule.finrank_mono hspan

end SchubertOrbits
