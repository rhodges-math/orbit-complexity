import OrbitComplexity.BruhatIntervals.Words.Subexpression
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Step counts of subexpressions

The change in Coxeter length at each selected letter is one or minus one. Summing these
changes counts the omitted and decreasing steps in terms of the final prefix length.
-/

namespace BruhatIntervals
noncomputable section

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
  {word : List S} (expression : Subexpression word)

private def indicator (p : Prop) : ℕ := @ite ℕ p (Classical.propDecidable p) 1 0

private theorem indicator_true {p : Prop} (hp : p) : indicator p = 1 := ite_eq_left hp
private theorem indicator_false {p : Prop} (hp : ¬p) : indicator p = 0 := ite_eq_right hp

private theorem unequal_step (j : Fin word.length)
    (h : expression.prefixProd cs j.val ≠ expression.prefixProd cs (j.val + 1)) :
    expression.prefixProd cs (j.val + 1) =
      expression.prefixProd cs j.val * cs.simple word[j.val] := by
  have hs := expression.prefixProd_succ cs j
  split_ifs at hs with hc
  · exact hs
  · exact (h (by simpa only [mul_one] using hs.symm)).elim

private theorem step_balance (j : Fin word.length) :
    indicator (expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1)) +
      2 * indicator (cs.BruhatLE (expression.prefixProd cs (j.val + 1))
        (expression.prefixProd cs j.val) ∧
          expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) +
        cs.length (expression.prefixProd cs (j.val + 1)) =
          cs.length (expression.prefixProd cs j.val) + 1 := by
  rcases mem_step_sets cs expression j with hp | he | hn
  · have hne : ¬(cs.BruhatLE (expression.prefixProd cs (j.val + 1))
        (expression.prefixProd cs j.val) ∧
          expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) :=
      fun hn => hp.2 (hp.1.antisymm hn.1)
    have hs := unequal_step cs expression j hp.2
    have hnd : ¬ cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val] := by
      intro hd
      have hdlen := cs.isRightDescent_iff.mp hd
      have hlen := hp.1.length_le
      rw [hs] at hlen
      omega
    have hl := cs.not_isRightDescent_iff.mp hnd
    rw [← hs] at hl
    rw [indicator_false hp.2, indicator_false hne]
    omega
  · have heq : expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1) := he
    have hne : ¬(cs.BruhatLE (expression.prefixProd cs (j.val + 1))
        (expression.prefixProd cs j.val) ∧
          expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) :=
      fun hn => hn.2 heq.symm
    rw [indicator_true heq, indicator_false hne]
    have hl := congrArg cs.length heq
    omega
  · have heq : expression.prefixProd cs j.val ≠ expression.prefixProd cs (j.val + 1) :=
      Ne.symm hn.2
    have hneg : cs.BruhatLE (expression.prefixProd cs (j.val + 1))
        (expression.prefixProd cs j.val) ∧
          expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val := hn
    have hs := unequal_step cs expression j heq
    have hd : cs.IsRightDescent (expression.prefixProd cs j.val) word[j.val] := by
      by_contra hnd
      have hl := cs.not_isRightDescent_iff.mp hnd
      have hlen := hn.1.length_le
      rw [hs] at hlen
      omega
    have hl := cs.isRightDescent_iff.mp hd
    rw [← hs] at hl
    rw [indicator_false heq, indicator_true hneg]
    omega

private theorem sum_balance (n : ℕ) (hn : n ≤ word.length) :
    (∑ j ∈ Finset.range n,
      indicator (expression.prefixProd cs j = expression.prefixProd cs (j + 1))) +
      2 * (∑ j ∈ Finset.range n,
        indicator (cs.BruhatLE (expression.prefixProd cs (j + 1)) (expression.prefixProd cs j) ∧
          expression.prefixProd cs (j + 1) ≠ expression.prefixProd cs j)) +
      cs.length (expression.prefixProd cs n) = n := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add,
      expression.prefixProd_zero, cs.length_one]
  | succ n ih =>
    have hi := ih (by omega)
    have hs := step_balance cs expression ⟨n, by omega⟩
    dsimp only at hs
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega

private theorem count_as_sum (s : Set (Fin word.length)) :
    s.ncard = ∑ j : Fin word.length, indicator (j ∈ s) := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine (Finset.card_eq_sum_ite (s := s.toFinset) (t := Finset.univ)
    (Finset.subset_univ _)).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ s
  · rw [ite_eq_left (Set.mem_toFinset.mpr hj), indicator_true hj]
  · rw [ite_eq_right (by simpa only [Set.mem_toFinset] using hj), indicator_false hj]

/-- Omitted steps and twice the decreasing steps account for the endpoint length. -/
theorem subexpression_step_count :
    (equalSteps cs expression).ncard + 2 * (negativeSteps cs expression).ncard +
      cs.length (expression.prefixProd cs word.length) = word.length := by
  have he := count_as_sum (s := equalSteps cs expression)
  have hn := count_as_sum (s := negativeSteps cs expression)
  change (equalSteps cs expression).ncard = ∑ j : Fin word.length,
    indicator (expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1)) at he
  change (negativeSteps cs expression).ncard = ∑ j : Fin word.length,
    indicator (cs.BruhatLE (expression.prefixProd cs (j.val + 1)) (expression.prefixProd cs j.val) ∧
      expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) at hn
  rw [he, hn, Fin.sum_univ_eq_sum_range (fun j =>
    indicator (expression.prefixProd cs j = expression.prefixProd cs (j + 1))),
    Fin.sum_univ_eq_sum_range (fun j =>
      indicator (cs.BruhatLE (expression.prefixProd cs (j + 1)) (expression.prefixProd cs j) ∧
        expression.prefixProd cs (j + 1) ≠ expression.prefixProd cs j))]
  exact sum_balance cs expression word.length (Nat.le_refl _)


end
end BruhatIntervals
