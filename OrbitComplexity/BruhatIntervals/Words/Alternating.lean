import TauCeti.GroupTheory.Coxeter.Parabolic

/-!
# Reduced words on two simple indices

A reduced word on two simple indices alternates whenever its product has a right ascent at the
first index. If their Coxeter exponent is finite, the length is strictly less than that exponent.

## Main results

* `reduced_word_eq_alternating`: a right ascent determines the alternating word.
* `alternating_length_lt`: its length is less than the finite Coxeter exponent.

## Implementation notes

`CoxeterSystem.alternatingWord i j n` has length `n` and ends at `j` when `n` is positive.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Proposition 4.2.5.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- A reduced word on `i` and `j` whose product has a right ascent at `i` alternates and ends
at `j` whenever it is nonempty. -/
theorem reduced_word_eq_alternating (i j : Index) {word : List Index}
    (hred : cs.IsReduced word) (hletters : ∀ a ∈ word, a = i ∨ a = j)
    (hascent : ¬ cs.IsRightDescent (cs.wordProd word) i) :
    word = CoxeterSystem.alternatingWord i j word.length := by
  induction word using List.reverseRecOn generalizing i j with
  | nil => rfl
  | append_singleton word a ih =>
    have hredword : cs.IsReduced word := by simpa using hred.take word.length
    have hnotlast : ¬ cs.IsRightDescent (cs.wordProd word) a := by
      rw [cs.not_isRightDescent_iff, hredword.eq]
      simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton] using hred.eq
    have hdesc : cs.IsRightDescent (cs.wordProd (word ++ [a])) a := by
      apply cs.isRightDescent_iff_not_isRightDescent_mul.mpr
      simpa only [cs.wordProd_append, cs.wordProd_singleton,
        cs.simple_mul_simple_cancel_right] using hnotlast
    rcases hletters a (by simp) with hai | haj
    · subst a
      exact False.elim (hascent hdesc)
    · subst a
      have hword := ih j i hredword
        (fun letter hletter => (hletters letter (List.mem_append_left [j] hletter)).symm)
        hnotlast
      rw [List.length_append, List.length_singleton, CoxeterSystem.alternatingWord_succ,
        List.concat_eq_append]
      exact congrArg (fun initial => initial ++ [j]) hword

/-- A reduced two-letter word whose product has a right ascent at its first index has length
less than the finite Coxeter exponent of the two indices. -/
theorem alternating_length_lt (i j : Index) {word : List Index}
    (hred : cs.IsReduced word) (hletters : ∀ a ∈ word, a = i ∨ a = j)
    (hascent : ¬ cs.IsRightDescent (cs.wordProd word) i) (hfinite : matrix i j ≠ 0) :
    word.length < matrix i j := by
  have hword := reduced_word_eq_alternating cs i j hred hletters hascent
  have hredsucc : cs.IsReduced (word ++ [i]) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, cs.wordProd_singleton,
      cs.not_isRightDescent_iff.mp hascent, hred.eq, List.length_append,
      List.length_singleton]
  have hredalt : cs.IsReduced (CoxeterSystem.alternatingWord j i (word.length + 1)) := by
    rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, ← hword]
    exact hredsucc
  by_contra hge
  exact cs.not_isReduced_alternatingWord j i (by rwa [matrix.symmetric j i])
    (by rw [matrix.symmetric j i]; omega) hredalt

end BruhatIntervals
