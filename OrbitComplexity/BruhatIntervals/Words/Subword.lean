import OrbitComplexity.BruhatIntervals.Words.Subexpression

/-!
# Subexpressions and subwords

The retained letters of a Boolean subexpression form a subword, and every subword is obtained
this way. Their products agree.

## Main definitions

* `Subexpression.selectedWord`: the retained letters of a subexpression.

## Main results

* `Subexpression.selectedWord_sublist`: retained letters form a subword.
* `exists_selectedWord_eq`: every subword arises from a subexpression.
* `Subexpression.wordProd_selectedWord`: subexpression and subword products agree.
* `subexpression_subword_property`: Bruhat comparison is the existence of a subexpression.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Section 2.2.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private def selectedLetters : List S → List Bool → List S
  | i :: word, choice :: choices =>
    if choice then i :: selectedLetters word choices else selectedLetters word choices
  | _, _ => []

private theorem selectedLetters_sublist (word : List S) (choices : List Bool) :
    (selectedLetters word choices).Sublist word := by
  induction word generalizing choices with
  | nil => simp only [selectedLetters, List.Sublist.refl]
  | cons i word ih =>
    cases choices with
    | nil => simp only [selectedLetters, List.nil_sublist]
    | cons choice choices =>
      cases choice
      · exact List.Sublist.cons i (ih choices)
      · exact List.Sublist.cons_cons i (ih choices)

private theorem selectedLetters_prod (word : List S) (choices : List Bool) :
    cs.wordProd (selectedLetters word choices) =
      ((word.zip choices).map (fun factor => if factor.2 then cs.simple factor.1 else 1)).prod := by
  induction word generalizing choices with
  | nil => simp only [selectedLetters, List.zip_nil_left, List.map_nil, List.prod_nil,
      cs.wordProd_nil]
  | cons i word ih =>
    cases choices with
    | nil => simp only [selectedLetters, List.zip_nil_right, List.map_nil, List.prod_nil,
        cs.wordProd_nil]
    | cons choice choices =>
      cases choice <;>
        simp only [selectedLetters, Bool.false_eq_true, ↓reduceIte,
          List.zip_cons_cons, List.map_cons, List.prod_cons, one_mul, cs.wordProd_cons, ih]

private theorem exists_selectedLetters {subword word : List S} (h : subword.Sublist word) :
    ∃ choices : List Bool, choices.length = word.length ∧
      selectedLetters word choices = subword := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons i _ ih =>
    obtain ⟨choices, hlength, hselected⟩ := ih
    exact ⟨false :: choices, by simpa only [List.length_cons] using congrArg (· + 1) hlength,
      by simpa only [selectedLetters, Bool.false_eq_true, ↓reduceIte] using hselected⟩
  | cons_cons i _ ih =>
    obtain ⟨choices, hlength, hselected⟩ := ih
    exact ⟨true :: choices, by simpa only [List.length_cons] using congrArg (· + 1) hlength,
      by simpa only [selectedLetters, ↓reduceIte] using congrArg (i :: ·) hselected⟩

namespace Subexpression

variable {word : List S} (expression : Subexpression word)

/-- The word obtained by retaining exactly the chosen letters of a subexpression. -/
def selectedWord : List S := selectedLetters word expression.choices

/-- The retained letters of a subexpression form a subword of its word. -/
theorem selectedWord_sublist : expression.selectedWord.Sublist word :=
  selectedLetters_sublist word expression.choices

/-- The product of the retained letters equals the product of the subexpression. -/
theorem wordProd_selectedWord :
    cs.wordProd expression.selectedWord = expression.prefixProd cs word.length := by
  rw [expression.prefixProd_length cs]
  exact selectedLetters_prod cs word expression.choices

end Subexpression

/-- Every subword is the retained word of a Boolean subexpression. -/
theorem exists_selectedWord_eq {subword word : List S} (h : subword.Sublist word) :
    ∃ expression : Subexpression word, expression.selectedWord = subword := by
  obtain ⟨choices, hlength, hselected⟩ := exists_selectedLetters h
  exact ⟨⟨choices, hlength⟩, hselected⟩

/-- For a fixed reduced word of `w`, an element is below `w` exactly when a subexpression
evaluates to it. -/
theorem subexpression_subword_property {u w : W} {word : List S} (hred : cs.IsReduced word)
    (hword : cs.wordProd word = w) :
    cs.BruhatLE u w ↔ ∃ expression : Subexpression word,
      expression.prefixProd cs word.length = u := by
  constructor
  · intro h
    obtain ⟨subword, hsub, hprod⟩ := (subword_property cs hred hword).mp h
    obtain ⟨expression, hselected⟩ := exists_selectedWord_eq hsub
    refine ⟨expression, ?_⟩
    rw [← expression.wordProd_selectedWord cs, hselected, hprod]
  · rintro ⟨expression, hprod⟩
    exact (subword_property cs hred hword).mpr
      ⟨expression.selectedWord, expression.selectedWord_sublist,
        (expression.wordProd_selectedWord cs).trans hprod⟩

end BruhatIntervals
