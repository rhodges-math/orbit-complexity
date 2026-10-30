import OrbitComplexity.BruhatIntervals.Words.Subexpression

/-! # Prefixes of subexpressions

Taking initial letters commutes with the choices, factors and prefix products of a
subexpression. Distinguished and positive subexpressions retain those properties on prefixes.

## Main definitions

* `Subexpression.take`: the subexpression on the first letters of its word.

## Main results

* `Subexpression.factors_take`: taking letters takes the same prefix of the factors.
* `Subexpression.prefixProd_take`: prefix products agree up to the truncation point.
* `IsDistinguished.take`: every prefix of a distinguished subexpression is distinguished.
* `IsPositive.take`: every prefix of a positive subexpression is positive.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W) {word : List Index}

namespace Subexpression

variable (expression : Subexpression word)

/-- The choices on the first `n` letters form a subexpression of the corresponding prefix. -/
def take (n : ℕ) : Subexpression (word.take n) where
  choices := expression.choices.take n
  length_choices := by simp only [List.length_take, expression.length_choices]

/-- A position of a prefix is the same numbered position in the original word. -/
def takePosition (n : ℕ) (j : Fin (word.take n).length) : Fin word.length :=
  ⟨j.val, lt_of_lt_of_le j.isLt (by
    simp only [List.length_take]
    exact Nat.min_le_right _ _)⟩

/-- Taking the first letters takes the same prefix of the subexpression factors. -/
theorem factors_take (n : ℕ) :
    (expression.take n).factors cs = (expression.factors cs).take n := by
  apply List.ext_getElem
  · simp only [length_factors, List.length_take]
  · intro i hi hi'
    simp only [factors, List.getElem_map, List.getElem_zip, List.getElem_take, take]

/-- Prefix products of a truncated subexpression agree up to its truncation point. -/
theorem prefixProd_take (n k : ℕ) :
    (expression.take n).prefixProd cs k = expression.prefixProd cs (min k n) := by
  simp only [prefixProd, factors_take, List.take_take, Nat.min_comm]

/-- An equal step in a prefix is exactly the corresponding equal step of the subexpression. -/
theorem equalSteps_take (n : ℕ) (j : Fin (word.take n).length) :
    j ∈ equalSteps cs (expression.take n) ↔
      takePosition n j ∈ equalSteps cs expression := by
  have hj : j.val < min n word.length := by simpa only [List.length_take] using j.isLt
  have hsucc : j.val + 1 ≤ n := by omega
  have hval : j.val ≤ n := by omega
  simp only [equalSteps, Set.mem_ofPred_eq, prefixProd_take, takePosition,
    Nat.min_eq_left hsucc, Nat.min_eq_left hval]

/-- A decreasing step in a prefix is exactly the corresponding decreasing step of the
subexpression. -/
theorem negativeSteps_take (n : ℕ) (j : Fin (word.take n).length) :
    j ∈ negativeSteps cs (expression.take n) ↔
      takePosition n j ∈ negativeSteps cs expression := by
  have hj : j.val < min n word.length := by simpa only [List.length_take] using j.isLt
  have hsucc : j.val + 1 ≤ n := by omega
  have hval : j.val ≤ n := by omega
  simp only [negativeSteps, Set.mem_ofPred_eq, prefixProd_take, takePosition,
    Nat.min_eq_left hsucc, Nat.min_eq_left hval]

end Subexpression

/-- Every prefix of a distinguished subexpression is distinguished. -/
theorem IsDistinguished.take {expression : Subexpression word}
    (hd : IsDistinguished cs expression) (n : ℕ) :
    IsDistinguished cs (expression.take n) := by
  intro j
  have hj : j.val < min n word.length := by simpa only [List.length_take] using j.isLt
  have hlen : j.val < word.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hsucc : j.val + 1 ≤ n := by omega
  have hval : j.val ≤ n := by omega
  simpa only [Subexpression.prefixProd_take, Nat.min_eq_left hsucc,
    Nat.min_eq_left hval, List.getElem_take] using hd ⟨j.val, hlen⟩

/-- Every prefix of a positive subexpression is positive. -/
theorem IsPositive.take {expression : Subexpression word}
    (hp : IsPositive cs expression) (n : ℕ) :
    IsPositive cs (expression.take n) := by
  intro j
  have hj : j.val < min n word.length := by simpa only [List.length_take] using j.isLt
  have hlen : j.val < word.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hsucc : j.val + 1 ≤ n := by omega
  have hval : j.val ≤ n := by omega
  simpa only [Subexpression.prefixProd_take, Nat.min_eq_left hsucc,
    Nat.min_eq_left hval] using hp ⟨j.val, hlen⟩

end BruhatIntervals
