import OrbitComplexity.BruhatIntervals.Order.Basic

/-!
# Subexpressions of words

Subexpressions replace chosen letters of a word by the identity. The adjacent prefix products
determine increasing, constant, and decreasing steps, as well as distinguished and positive
subexpressions.

## Main definitions

* `Subexpression`: a Boolean choice for each letter of a word.
* `Subexpression.prefixProd`: products of the first letters with their choices.
* `positiveSteps`, `equalSteps`, `negativeSteps`: the three classes of adjacent prefixes.
* `IsDistinguished`: each next prefix lies below multiplication by the next simple reflection.
* `IsPositive`: adjacent prefixes increase weakly in Bruhat order.

## Implementation notes

A position `j : Fin word.length` denotes the letter numbered `j + 1`. Prefix `k` contains exactly
the first `k` factors, so prefix `0` is the identity and the adjacent prefixes at `j` are `j` and
`j + 1`.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Representation Theory 8 (2004),
  212–242, Section 3.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- A subexpression of a word chooses whether to keep each of its letters. -/
structure Subexpression (word : List S) where
  /-- The choices, with `true` keeping the simple reflection and `false` replacing it by `1`. -/
  choices : List Bool
  /-- There is one choice for each letter of the word. -/
  length_choices : choices.length = word.length

namespace Subexpression

variable {word : List S} (expression : Subexpression word)

/-- The factors of a subexpression, after replacing unchosen letters by the identity. -/
def factors : List W :=
  (word.zip expression.choices).map (fun factor => if factor.2 then cs.simple factor.1 else 1)

/-- The number of factors of a subexpression equals the length of its word. -/
theorem length_factors : (expression.factors cs).length = word.length := by
  simp only [factors, List.length_map, List.length_zip, expression.length_choices, Nat.min_self]

/-- The product of the first `k` factors of a subexpression. -/
def prefixProd (k : ℕ) : W := ((expression.factors cs).take k).prod

/-- The prefix with no factors is the identity. -/
theorem prefixProd_zero : expression.prefixProd cs 0 = 1 := by
  simp only [prefixProd, List.take_zero, List.prod_nil]

/-- The prefix with every factor is the product of the factors of the subexpression. -/
theorem prefixProd_length :
    expression.prefixProd cs word.length = (expression.factors cs).prod := by
  rw [prefixProd, ← expression.length_factors cs, List.take_length]

/-- At position `j`, the next prefix is obtained by multiplying by its chosen factor. -/
theorem prefixProd_succ (j : Fin word.length) :
    expression.prefixProd cs (j.val + 1) = expression.prefixProd cs j.val *
      (if expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt)
        then cs.simple word[j.val] else 1) := by
  have hpos : j.val < (expression.factors cs).length := by
    rw [expression.length_factors cs]
    exact j.isLt
  rw [prefixProd, List.prod_take_succ _ _ hpos]
  simp only [factors, List.getElem_map, List.getElem_zip, prefixProd]

end Subexpression

variable {word : List S}

/-- The positions at which adjacent prefix products increase strictly in Bruhat order. -/
def positiveSteps (expression : Subexpression word) : Set (Fin word.length) :=
  {j | cs.BruhatLE (expression.prefixProd cs j.val) (expression.prefixProd cs (j.val + 1)) ∧
    expression.prefixProd cs j.val ≠ expression.prefixProd cs (j.val + 1)}

/-- The positions at which adjacent prefix products are equal. -/
def equalSteps (expression : Subexpression word) : Set (Fin word.length) :=
  {j | expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1)}

/-- The positions at which adjacent prefix products decrease strictly in Bruhat order. -/
def negativeSteps (expression : Subexpression word) : Set (Fin word.length) :=
  {j | cs.BruhatLE (expression.prefixProd cs (j.val + 1)) (expression.prefixProd cs j.val) ∧
    expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val}

/-- A subexpression is distinguished when each next prefix is below the previous prefix times the
corresponding simple reflection. -/
def IsDistinguished (expression : Subexpression word) : Prop :=
  ∀ j : Fin word.length, cs.BruhatLE (expression.prefixProd cs (j.val + 1))
    (expression.prefixProd cs j.val * cs.simple word[j.val])

/-- A subexpression is positive when each prefix is below the following prefix. -/
def IsPositive (expression : Subexpression word) : Prop :=
  ∀ j : Fin word.length,
    cs.BruhatLE (expression.prefixProd cs j.val) (expression.prefixProd cs (j.val + 1))

/-- Adjacent prefixes of a subexpression are comparable in Bruhat order. -/
theorem prefixProd_comparable (expression : Subexpression word) (j : Fin word.length) :
    cs.BruhatLE (expression.prefixProd cs j.val) (expression.prefixProd cs (j.val + 1)) ∨
    cs.BruhatLE (expression.prefixProd cs (j.val + 1)) (expression.prefixProd cs j.val) := by
  rw [expression.prefixProd_succ cs j]
  split
  · by_cases hdesc : cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val]
    · exact Or.inr (cs.bruhatStep_mul_simple_of_isRightDescent _ hdesc).bruhatLE
    · exact Or.inl (cs.bruhatStep_mul_simple _ (by
        rw [cs.not_isRightDescent_iff.mp hdesc]
        exact Nat.lt_succ_self _)).bruhatLE
  · rw [mul_one]
    exact Or.inl (cs.bruhatLE_refl _)

/-- A subexpression is distinguished exactly when every right descent of the preceding prefix
forces the corresponding letter to be chosen. -/
theorem isDistinguished_iff_forced (expression : Subexpression word) :
    IsDistinguished cs expression ↔
      ∀ j : Fin word.length,
        cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val] →
        expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) = true := by
  constructor
  · intro h j hdesc
    by_contra hchoice
    have heq : expression.prefixProd cs (j.val + 1) = expression.prefixProd cs j.val := by
      rw [expression.prefixProd_succ cs j]
      simp only [hchoice, ↓reduceIte, mul_one]
    have hle := h j
    rw [heq] at hle
    exact (Nat.not_lt_of_ge hle.length_le) hdesc
  · intro h j
    rw [expression.prefixProd_succ cs j]
    split
    · exact cs.bruhatLE_refl _
    · rename_i hchoice
      rw [mul_one]
      have hdesc : ¬ cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val] :=
        fun hdesc => hchoice (h j hdesc)
      exact (cs.bruhatStep_mul_simple _ (by
        rw [cs.not_isRightDescent_iff.mp hdesc]
        exact Nat.lt_succ_self _)).bruhatLE

/-- Positivity is equivalent to the absence of decreasing steps. -/
theorem isPositive_iff_negativeSteps_empty (expression : Subexpression word) :
    IsPositive cs expression ↔ negativeSteps cs expression = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro j ⟨hdown, hne⟩
    exact hne (hdown.antisymm (h j))
  · intro h j
    rcases prefixProd_comparable cs expression j with hup | hdown
    · exact hup
    · by_cases heq : expression.prefixProd cs (j.val + 1) = expression.prefixProd cs j.val
      · rw [heq]
      · have hmem : j ∈ negativeSteps cs expression := ⟨hdown, heq⟩
        rw [h] at hmem
        exact False.elim hmem

/-- Every position of a subexpression is increasing, constant, or decreasing. -/
theorem mem_step_sets (expression : Subexpression word) (j : Fin word.length) :
    j ∈ positiveSteps cs expression ∨ j ∈ equalSteps cs expression ∨
      j ∈ negativeSteps cs expression := by
  by_cases heq : expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1)
  · exact Or.inr (Or.inl heq)
  · rcases prefixProd_comparable cs expression j with hup | hdown
    · exact Or.inl ⟨hup, heq⟩
    · exact Or.inr (Or.inr ⟨hdown, Ne.symm heq⟩)

/-- Subexpressions, prefixes, step sets, and distinguished and positive conditions satisfy their
defining properties. -/
theorem subexpression_definitions (expression : Subexpression word) (k : ℕ)
    (j : Fin word.length) :
    expression.choices.length = word.length ∧
    expression.factors cs = (word.zip expression.choices).map
      (fun factor => if factor.2 then cs.simple factor.1 else 1) ∧
    expression.prefixProd cs k = ((expression.factors cs).take k).prod ∧
    (j ∈ positiveSteps cs expression ↔
      cs.BruhatLE (expression.prefixProd cs j.val) (expression.prefixProd cs (j.val + 1)) ∧
      expression.prefixProd cs j.val ≠ expression.prefixProd cs (j.val + 1)) ∧
    (j ∈ equalSteps cs expression ↔
      expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1)) ∧
    (j ∈ negativeSteps cs expression ↔
      cs.BruhatLE (expression.prefixProd cs (j.val + 1)) (expression.prefixProd cs j.val) ∧
      expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) ∧
    (IsDistinguished cs expression ↔
      ∀ p : Fin word.length, cs.BruhatLE (expression.prefixProd cs (p.val + 1))
        (expression.prefixProd cs p.val * cs.simple word[p.val])) ∧
    (IsPositive cs expression ↔ ∀ p : Fin word.length,
      cs.BruhatLE (expression.prefixProd cs p.val) (expression.prefixProd cs (p.val + 1))) :=
  ⟨expression.length_choices, rfl, rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

end BruhatIntervals
