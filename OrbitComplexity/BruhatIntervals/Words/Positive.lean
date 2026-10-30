import OrbitComplexity.BruhatIntervals.Words.Subexpression

/-! # Positive distinguished subexpressions

The last letter of a positive distinguished subexpression is determined by the right descent
of its final product. Repeating this choice backwards gives existence and uniqueness for
every element below the product of a fixed reduced word.

## Main results

* `positive_subexpression_unique`: existence and uniqueness of the positive distinguished
  subexpression with prescribed product.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Representation Theory 8
  (2004), 212–242, Lemma 3.5.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private theorem choices_ext {word : List S} {left right : Subexpression word}
    (h : left.choices = right.choices) : left = right := by
  cases left
  cases right
  cases h
  rfl

private def appendExpression {word : List S} (expression : Subexpression word) (i : S)
    (keep : Bool) : Subexpression (word ++ [i]) :=
  ⟨expression.choices ++ [keep], by simp [expression.length_choices]⟩

private theorem append_factors {word : List S} (expression : Subexpression word) (i : S)
    (keep : Bool) :
    (appendExpression expression i keep).factors cs =
      expression.factors cs ++ [if keep then cs.simple i else 1] := by
  simp only [Subexpression.factors, appendExpression]
  rw [List.zip_append expression.length_choices.symm]
  simp only [List.map_append, List.zip_cons_cons, List.zip_nil_left, List.map_cons,
    List.map_nil]

private theorem append_prefix {word : List S} (expression : Subexpression word) (i : S)
    (keep : Bool) (k : ℕ) (hk : k ≤ word.length) :
    (appendExpression expression i keep).prefixProd cs k = expression.prefixProd cs k := by
  simp only [Subexpression.prefixProd, append_factors]
  rw [List.take_append_of_le_length (by simpa [expression.length_factors cs] using hk)]

private theorem append_final {word : List S} (expression : Subexpression word) (i : S)
    (keep : Bool) :
    (appendExpression expression i keep).prefixProd cs (word.length + 1) =
      expression.prefixProd cs word.length * (if keep then cs.simple i else 1) := by
  simpa only [List.length_append, List.length_singleton, append_factors,
    List.prod_append, List.prod_singleton, Subexpression.prefixProd_length] using
      (appendExpression expression i keep).prefixProd_length cs

private theorem exists_append {word : List S} (i : S)
    (expression : Subexpression (word ++ [i])) :
    ∃ previous : Subexpression word, ∃ keep : Bool,
      appendExpression previous i keep = expression := by
  have hne : expression.choices ≠ [] := by
    intro h
    have := expression.length_choices
    simp [h] at this
  let previous : Subexpression word :=
    ⟨expression.choices.dropLast, by simp [expression.length_choices]⟩
  refine ⟨previous, expression.choices.getLast hne, choices_ext ?_⟩
  exact List.dropLast_append_getLast hne

private theorem positive_distinguished_iff {word : List S}
    (expression : Subexpression word) :
    (IsDistinguished cs expression ∧ IsPositive cs expression) ↔
      ∀ j : Fin word.length,
        ¬ cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val] := by
  constructor
  · intro h j hdesc
    have hle := (h.2 j).trans (h.1 j)
    exact (Nat.not_lt_of_ge hle.length_le) hdesc
  · intro h
    refine ⟨(isDistinguished_iff_forced cs expression).mpr (fun j hd => (h j hd).elim), ?_⟩
    intro j
    rw [expression.prefixProd_succ cs j]
    split
    · exact (cs.bruhatStep_mul_simple _ (by
        rw [cs.not_isRightDescent_iff.mp (h j)]
        exact Nat.lt_succ_self _)).bruhatLE
    · rw [mul_one]

private theorem append_conditions {word : List S} (expression : Subexpression word) (i : S)
    (keep : Bool) :
    (IsDistinguished cs (appendExpression expression i keep) ∧
      IsPositive cs (appendExpression expression i keep)) ↔
      (IsDistinguished cs expression ∧ IsPositive cs expression) ∧
        ¬ cs.IsRightDescent (expression.prefixProd cs word.length) i := by
  simp only [positive_distinguished_iff]
  constructor
  · intro h
    constructor
    · intro j
      have hj := h ⟨j.val, by simp only [List.length_append, List.length_singleton]; omega⟩
      rw [append_prefix cs expression i keep _ (Nat.le_of_lt j.isLt)] at hj
      simpa only [List.getElem_append, j.isLt, ↓reduceDIte] using hj
    · have hj := h ⟨word.length, by simp⟩
      rw [append_prefix cs expression i keep _ (Nat.le_refl _)] at hj
      simpa using hj
  · rintro ⟨h, hi⟩ j
    by_cases hj : j.val < word.length
    · rw [append_prefix cs expression i keep _ (Nat.le_of_lt hj)]
      simpa only [List.getElem_append, hj, ↓reduceDIte] using h ⟨j.val, hj⟩
    · have hlast : j.val = word.length := by
        have := j.isLt
        simp only [List.length_append, List.length_singleton] at this
        omega
      simpa [hlast, append_prefix cs expression i keep _ (Nat.le_refl _)] using hi

/-- A fixed reduced word has a unique positive distinguished subexpression for each element
below its product. This is Marsh–Rietsch, Lemma 3.5. -/
theorem positive_subexpression_unique {word : List S} (hred : cs.IsReduced word)
    (u : W) (hle : cs.BruhatLE u (cs.wordProd word)) :
    ∃! expression : Subexpression word,
      expression.prefixProd cs word.length = u ∧
      IsDistinguished cs expression ∧ IsPositive cs expression := by
  classical
  induction word using List.reverseRecOn generalizing u with
  | nil =>
      have hu : u = 1 := cs.bruhatLE_one_iff.mp (by simpa using hle)
      subst u
      refine ⟨⟨[], rfl⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro expression _
        apply choices_ext
        exact List.eq_nil_of_length_eq_zero expression.length_choices
  | append_singleton word i ih =>
      have hprevious : cs.IsReduced word := by simpa using hred.take word.length
      have hlength : cs.length (cs.wordProd word * cs.simple i) = word.length + 1 := by
        simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
          List.length_singleton] using hred.eq
      have hdescent : cs.IsRightDescent (cs.wordProd (word ++ [i])) i := by
        rw [cs.isRightDescent_iff, cs.wordProd_append, cs.wordProd_singleton,
          cs.simple_mul_simple_cancel_right, hprevious.eq, hlength]
      by_cases hu : cs.IsRightDescent u i
      · have hbelow : cs.BruhatLE (u * cs.simple i) (cs.wordProd word) := by
          have h := (bruhatLE_descent_iff cs i hu hdescent).mp hle
          simpa only [cs.wordProd_append, cs.wordProd_singleton,
            cs.simple_mul_simple_cancel_right] using h
        obtain ⟨expression, hspec, huniq⟩ := ih hprevious (u * cs.simple i) hbelow
        have hascent : ¬ cs.IsRightDescent (expression.prefixProd cs word.length) i := by
          rw [hspec.1]
          exact cs.isRightDescent_iff_not_isRightDescent_mul.mp hu
        refine ⟨appendExpression expression i true, ⟨?_, ?_⟩, ?_⟩
        · simp only [List.length_append, List.length_singleton, append_final,
            ↓reduceIte, hspec.1, cs.simple_mul_simple_cancel_right]
        · exact (append_conditions cs expression i true).mpr ⟨hspec.2, hascent⟩
        · intro other hother
          obtain ⟨previous, keep, rfl⟩ := exists_append i other
          have hgood := (append_conditions cs previous i keep).mp hother.2
          have hfinal := hother.1
          simp only [List.length_append, List.length_singleton, append_final] at hfinal
          cases keep with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hfinal
              have hnot : ¬ cs.IsRightDescent u i := by simpa only [hfinal] using hgood.2
              exact (hnot hu).elim
          | true =>
              simp only [↓reduceIte] at hfinal
              have hvalue : previous.prefixProd cs word.length = u * cs.simple i := by
                simpa only [cs.simple_mul_simple_cancel_right] using
                  congrArg (fun w => w * cs.simple i) hfinal
              exact congrArg (fun e => appendExpression e i true)
                (huniq previous ⟨hvalue, hgood.1⟩)
      · have hbelow : cs.BruhatLE u (cs.wordProd word) := by
          have h := bruhatLE_mul_of_ascent cs hle i hu
          simpa only [cs.wordProd_append, cs.wordProd_singleton,
            cs.simple_mul_simple_cancel_right] using h
        obtain ⟨expression, hspec, huniq⟩ := ih hprevious u hbelow
        have hascent : ¬ cs.IsRightDescent (expression.prefixProd cs word.length) i := by
          rwa [hspec.1]
        refine ⟨appendExpression expression i false, ⟨?_, ?_⟩, ?_⟩
        · simpa only [List.length_append, List.length_singleton, append_final,
            Bool.false_eq_true, ↓reduceIte, mul_one] using hspec.1
        · exact (append_conditions cs expression i false).mpr ⟨hspec.2, hascent⟩
        · intro other hother
          obtain ⟨previous, keep, rfl⟩ := exists_append i other
          have hgood := (append_conditions cs previous i keep).mp hother.2
          have hfinal := hother.1
          simp only [List.length_append, List.length_singleton, append_final] at hfinal
          cases keep with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hfinal
              exact congrArg (fun e => appendExpression e i false)
                (huniq previous ⟨hfinal, hgood.1⟩)
          | true =>
              simp only [↓reduceIte] at hfinal
              have hnot : ¬ cs.IsRightDescent (u * cs.simple i) i := by
                rw [← hfinal, cs.simple_mul_simple_cancel_right]
                exact hgood.2
              exact (hu (cs.isRightDescent_iff_not_isRightDescent_mul.mpr hnot)).elim

end BruhatIntervals
