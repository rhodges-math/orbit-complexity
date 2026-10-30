import OrbitComplexity.BruhatIntervals.Words.Support

/-!
# Reduced words with distinct simple reflections

The support size is bounded by Coxeter length. Equality holds exactly when every reduced
expression has distinct simple reflections, and it is equivalent to zero length-minus-support.

## Main results

* `distinct_reduced_words`: zero numerical defect, equal length and support, and distinct letters
  in every reduced expression are equivalent.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

universe u v

variable {Index : Type u} {W : Type v} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- Zero length-minus-support is equivalent to equality of length and support, which in turn
is equivalent to distinct simple reflections in every reduced expression. -/
theorem distinct_reduced_words (w : W) :
    (cs.length w - supportCard cs w = 0 ↔ cs.length w = supportCard cs w) ∧
    (cs.length w = supportCard cs w ↔
      ∀ word : List Index, cs.IsReduced word → cs.wordProd word = w →
        (word.map cs.simple).Nodup) := by
  constructor
  · have hbound := supportCard_le_length cs w
    omega
  · constructor
    · intro heq word hred hword
      exact (supportCard_eq_length_iff cs hred hword).mp heq.symm
    · intro hdistinct
      obtain ⟨word, hred, hword⟩ := cs.exists_isReduced w
      exact ((supportCard_eq_length_iff cs hred hword.symm).mpr
        (hdistinct word hred hword.symm)).symm

end BruhatIntervals
