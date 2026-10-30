import OrbitComplexity.BruhatIntervals.Graph.Basic
import OrbitComplexity.BruhatIntervals.Realizations.Conjugation
import OrbitComplexity.BruhatIntervals.Words.Prefix

/-! # Roots attached to subexpression positions

An omitted position carries the preceding prefix image of its simple root. At a decreasing
position the negative of that image is positive. These are the positive labels of the
corresponding Bruhat edges.

## Main definitions

* `SchubertOrbits.subwordRoot`: the signed root at a position of a subexpression.
* `SchubertOrbits.subwordWeightSpan`: the span of the roots at omitted and decreasing positions.
* `SchubertOrbits.subwordWeightDim`: the dimension of that span.

## Main results

* `SchubertOrbits.subwordRoot_positive`: the roots at omitted and decreasing positions are
  positive for a distinguished subexpression.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  Definition 3.19.
-/

open BruhatIntervals

namespace SchubertOrbits

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V)) {word : List Index}
  (expression : Subexpression word)

/-- The preceding simple-root image, negated at a decreasing position. Its values at omitted
and decreasing positions are the roots attached to the subexpression. -/
noncomputable def subwordRoot (j : Fin word.length) : V := by
  classical
  exact if j ∈ negativeSteps cs expression then
    -realization.action (expression.prefixProd cs j.val) (realization.simpleRoot word[j.val])
  else realization.action (expression.prefixProd cs j.val) (realization.simpleRoot word[j.val])

private theorem negative_prefix (j : Fin word.length)
    (hj : j ∈ negativeSteps cs expression) :
    expression.prefixProd cs (j.val + 1) =
      expression.prefixProd cs j.val * cs.simple word[j.val] := by
  have h := expression.prefixProd_succ cs j
  split at h
  · exact h
  · simp only [mul_one] at h
    exact False.elim (hj.2 h)

private theorem equal_not_negative (j : Fin word.length)
    (hj : j ∈ equalSteps cs expression) : j ∉ negativeSteps cs expression := by
  intro hnegative
  exact hnegative.2 hj.symm

/-- At an omitted position the attached root is the preceding prefix image of the simple root. -/
theorem subwordRoot_of_equal (j : Fin word.length) (hj : j ∈ equalSteps cs expression) :
    subwordRoot realization expression j =
      realization.action (expression.prefixProd cs j.val) (realization.simpleRoot word[j.val]) := by
  classical
  exact ite_eq_right (equal_not_negative expression j hj)

/-- At a decreasing position the attached root is the negative preceding simple-root image. -/
theorem subwordRoot_of_negative (j : Fin word.length)
    (hj : j ∈ negativeSteps cs expression) :
    subwordRoot realization expression j =
      -realization.action (expression.prefixProd cs j.val)
        (realization.simpleRoot word[j.val]) := by
  classical
  exact ite_eq_left hj

/-- Every omitted or decreasing position of a distinguished subexpression has a positive root. -/
theorem subwordRoot_positive (hd : IsDistinguished cs expression) (j : Fin word.length)
    (hj : j ∈ equalSteps cs expression ∨ j ∈ negativeSteps cs expression) :
    subwordRoot realization expression j ∈ realization.positiveRoots := by
  rcases hj with hequal | hnegative
  · rw [subwordRoot_of_equal realization expression j hequal]
    apply realization.action_simpleRoot_positive
    intro hdesc
    have hle := hd j
    change expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1) at hequal
    rw [← hequal] at hle
    exact (Nat.not_lt_of_ge hle.length_le) hdesc
  · rw [subwordRoot_of_negative realization expression j hnegative]
    apply realization.action_simpleRoot_negative
    change cs.length (expression.prefixProd cs j.val * cs.simple word[j.val]) <
      cs.length (expression.prefixProd cs j.val)
    rw [← negative_prefix expression j hnegative]
    exact hnegative.1.length_lt_of_ne hnegative.2

private theorem simple_root_reflection (i : Index) :
    (realization.rootReflection
      ⟨realization.simpleRoot i, realization.simpleRoot_mem_positiveRoots i⟩).val =
      cs.simple i := by
  apply realization.action_injective
  apply LinearEquiv.ext
  intro y
  rw [realization.rootReflection_apply, realization.action_simple]

/-- The reflection of an attached positive root is the conjugated simple reflection. -/
theorem subwordRoot_reflection (hd : IsDistinguished cs expression) (j : Fin word.length)
    (hj : j ∈ equalSteps cs expression ∨ j ∈ negativeSteps cs expression) :
    (realization.rootReflection
      ⟨subwordRoot realization expression j,
        subwordRoot_positive realization expression hd j hj⟩).val =
      expression.prefixProd cs j.val * cs.simple word[j.val] *
        (expression.prefixProd cs j.val)⁻¹ := by
  have hpos := subwordRoot_positive realization expression hd j hj
  rcases hj with hequal | hnegative
  · rw [subwordRoot_of_equal realization expression j hequal] at hpos
    have heq : (⟨subwordRoot realization expression j,
        subwordRoot_positive realization expression hd j (Or.inl hequal)⟩ :
        {root : V // root ∈ realization.positiveRoots}) =
        ⟨realization.action (expression.prefixProd cs j.val)
          (realization.simpleRoot word[j.val]), hpos⟩ :=
      Subtype.ext (subwordRoot_of_equal realization expression j hequal)
    rw [heq]
    exact realization.rootReflection_translated_simple _ _ hpos
  · rw [subwordRoot_of_negative realization expression j hnegative] at hpos
    have heq : (⟨subwordRoot realization expression j,
        subwordRoot_positive realization expression hd j (Or.inr hnegative)⟩ :
        {root : V // root ∈ realization.positiveRoots}) =
        ⟨-realization.action (expression.prefixProd cs j.val)
          (realization.simpleRoot word[j.val]), hpos⟩ :=
      Subtype.ext (subwordRoot_of_negative realization expression j hnegative)
    rw [heq]
    have h := realization.rootReflection_conj_neg (expression.prefixProd cs j.val)
      ⟨realization.simpleRoot word[j.val], realization.simpleRoot_mem_positiveRoots _⟩ hpos
    rwa [simple_root_reflection realization] at h

/-- An attached root is the positive label of the simple edge at its preceding prefix. -/
theorem subwordRoot_eq_edgeLabel (hd : IsDistinguished cs expression) (j : Fin word.length)
    (hj : j ∈ equalSteps cs expression ∨ j ∈ negativeSteps cs expression) :
    subwordRoot realization expression j = edgeLabel realization
      (expression.prefixProd cs j.val)
      (expression.prefixProd cs j.val * cs.simple word[j.val])
      ((cs.isReflection_simple word[j.val]).conj (expression.prefixProd cs j.val)) := by
  symm
  apply edgeLabel_unique realization _
    ⟨subwordRoot realization expression j, subwordRoot_positive realization expression hd j hj⟩
  rw [subwordRoot_reflection realization expression hd j hj]
  group

/-- At a decreasing position the root labels the edge from the next prefix to the preceding one. -/
theorem subwordRoot_negative_edge (hd : IsDistinguished cs expression) (j : Fin word.length)
    (hj : j ∈ negativeSteps cs expression) :
    ∃ h : (bruhatGraph cs).Adj (expression.prefixProd cs (j.val + 1))
        (expression.prefixProd cs j.val),
      subwordRoot realization expression j = edgeLabel realization
        (expression.prefixProd cs (j.val + 1)) (expression.prefixProd cs j.val) h := by
  have h := (cs.isReflection_simple word[j.val]).conj (expression.prefixProd cs j.val)
  have hadj : (bruhatGraph cs).Adj (expression.prefixProd cs j.val)
      (expression.prefixProd cs j.val * cs.simple word[j.val]) := h
  have hnext := negative_prefix expression j hj
  have hreverse : (bruhatGraph cs).Adj (expression.prefixProd cs (j.val + 1))
      (expression.prefixProd cs j.val) := by
    rw [hnext]
    exact (bruhatGraph cs).adj_symm hadj
  refine ⟨hreverse, ?_⟩
  have heq := (subwordRoot_eq_edgeLabel realization expression hd j (Or.inr hj)).trans
    (edgeLabel_symm realization _ _ hadj)
  simpa only [hnext] using heq

/-- Truncation preserves the attached root at every remaining position. -/
theorem subwordRoot_take (n : ℕ) (j : Fin (word.take n).length) :
    subwordRoot realization (expression.take n) j = subwordRoot realization expression
      (Subexpression.takePosition n j) := by
  classical
  have hj : j.val < min n word.length := by simpa only [List.length_take] using j.isLt
  have hval : j.val ≤ n := by omega
  simp only [subwordRoot, Subexpression.negativeSteps_take, Subexpression.prefixProd_take,
    Nat.min_eq_left hval, List.getElem_take, Subexpression.takePosition]
  rfl

/-- The real span of the roots at omitted and decreasing positions of the subexpression. -/
noncomputable def subwordWeightSpan : Submodule ℝ V :=
  Submodule.span ℝ ((subwordRoot realization expression) ''
    (equalSteps cs expression ∪ negativeSteps cs expression))

/-- The span of the finitely many attached roots is finite-dimensional. -/
instance subwordWeightSpan_finiteDimensional :
    FiniteDimensional ℝ (subwordWeightSpan realization expression) :=
  FiniteDimensional.span_of_finite ℝ (Set.toFinite _)

/-- The dimension of the real span of the attached roots. -/
noncomputable def subwordWeightDim : ℕ :=
  Module.finrank ℝ (subwordWeightSpan realization expression)

/-- Negating the attached roots preserves their real span. -/
theorem subwordWeightSpan_eq_neg :
    subwordWeightSpan realization expression = Submodule.span ℝ
      ((fun j => -subwordRoot realization expression j) ''
        (equalSteps cs expression ∪ negativeSteps cs expression)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨j, hj, rfl⟩
    have h : -subwordRoot realization expression j ∈ Submodule.span ℝ
        ((fun j => -subwordRoot realization expression j) ''
          (equalSteps cs expression ∪ negativeSteps cs expression)) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    change subwordRoot realization expression j ∈ Submodule.span ℝ
      ((fun j => -subwordRoot realization expression j) ''
        (equalSteps cs expression ∪ negativeSteps cs expression))
    simpa only [neg_neg] using Submodule.neg_mem _ h
  · apply Submodule.span_le.mpr
    rintro α ⟨j, hj, rfl⟩
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-- The roots of a prefix span a subspace of the original subexpression's root span. -/
theorem subwordWeightSpan_take_le (n : ℕ) :
    subwordWeightSpan realization (expression.take n) ≤
      subwordWeightSpan realization expression := by
  apply Submodule.span_le.mpr
  rintro α ⟨j, hj, rfl⟩
  change subwordRoot realization (expression.take n) j ∈ subwordWeightSpan realization expression
  rw [subwordRoot_take realization expression]
  apply Submodule.subset_span
  refine ⟨Subexpression.takePosition n j, ?_, rfl⟩
  rcases hj with hequal | hnegative
  · exact Or.inl ((expression.equalSteps_take cs n j).mp hequal)
  · exact Or.inr ((expression.negativeSteps_take cs n j).mp hnegative)

private theorem subwordRoot_mem_prefix (j k : Fin word.length)
    (hk : k ∈ equalSteps cs expression ∪ negativeSteps cs expression) (hlt : k.val < j.val) :
    subwordRoot realization expression k ∈
      subwordWeightSpan realization (expression.take j.val) := by
  let position : Fin (word.take j.val).length := ⟨k.val, by
    simpa only [List.length_take, Nat.min_eq_left j.isLt.le] using hlt⟩
  have heq : Subexpression.takePosition j.val position = k := Fin.ext rfl
  have hposition : position ∈ equalSteps cs (expression.take j.val) ∪
      negativeSteps cs (expression.take j.val) := by
    rcases hk with hequal | hnegative
    · apply Or.inl
      apply (expression.equalSteps_take cs j.val position).mpr
      simpa only [heq] using hequal
    · apply Or.inr
      apply (expression.negativeSteps_take cs j.val position).mpr
      simpa only [heq] using hnegative
  have hroot : subwordRoot realization (expression.take j.val) position =
      subwordRoot realization expression k := by
    rw [subwordRoot_take realization expression, heq]
  rw [← hroot]
  exact Submodule.subset_span ⟨position, hposition, rfl⟩

/-- An omitted or decreasing last position adds exactly its root line to the prefix span. -/
theorem subwordWeightSpan_last (j : Fin word.length) (hlast : j.val + 1 = word.length)
    (hj : j ∈ equalSteps cs expression ∪ negativeSteps cs expression) :
    subwordWeightSpan realization expression =
      subwordWeightSpan realization (expression.take j.val) ⊔
        Submodule.span ℝ {subwordRoot realization expression j} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨k, hk, rfl⟩
    by_cases heq : k = j
    · subst k
      exact (le_sup_right : Submodule.span ℝ {subwordRoot realization expression j} ≤ _)
        (Submodule.subset_span (Set.mem_singleton _))
    · have hne : k.val ≠ j.val := fun h => heq (Fin.ext h)
      have hlt : k.val < j.val := by have h := k.isLt; omega
      exact (le_sup_left : subwordWeightSpan realization (expression.take j.val) ≤ _)
        (subwordRoot_mem_prefix realization expression j k hk hlt)
  · apply sup_le
    · exact subwordWeightSpan_take_le realization expression j.val
    · apply Submodule.span_le.mpr
      intro α hα
      have heq : α = subwordRoot realization expression j := Set.mem_singleton_iff.mp hα
      rw [heq]
      exact Submodule.subset_span ⟨j, hj, rfl⟩

/-- An increasing last position leaves the span of the attached roots unchanged. -/
theorem subwordWeightSpan_last_positive (j : Fin word.length)
    (hlast : j.val + 1 = word.length) (hj : j ∈ positiveSteps cs expression) :
    subwordWeightSpan realization expression =
      subwordWeightSpan realization (expression.take j.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨k, hk, rfl⟩
    have heq : k ≠ j := by
      intro heq
      subst k
      rcases hk with hequal | hnegative
      · exact hj.2 hequal
      · exact hj.2 (hj.1.antisymm hnegative.1)
    have hne : k.val ≠ j.val := fun h => heq (Fin.ext h)
    have hlt : k.val < j.val := by have h := k.isLt; omega
    exact subwordRoot_mem_prefix realization expression j k hk hlt
  · exact subwordWeightSpan_take_le realization expression j.val

end SchubertOrbits
