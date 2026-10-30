import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! Extremal sums of a fixed number of labels, retaining all zero heights. -/

open scoped BigOperators

namespace FrobeniusSplitting

/-- Selecting as many labels as there are positive heights gives a unique maximal sum. -/
theorem positive_sum_max {I : Type*} [Fintype I] (h : I → ℤ) (s : Finset I)
    (hc : s.card = (Finset.univ.filter (fun i => 0 < h i)).card) :
    let P := Finset.univ.filter (fun i => 0 < h i)
    (∑ i ∈ s, h i) ≤ ∑ i ∈ P, h i ∧
      ((∑ i ∈ s, h i) = ∑ i ∈ P, h i ↔ s = P) := by
  classical
  let P := Finset.univ.filter (fun i => 0 < h i)
  change s.card = P.card at hc
  change (∑ i ∈ s, h i) ≤ ∑ i ∈ P, h i ∧
    ((∑ i ∈ s, h i) = ∑ i ∈ P, h i ↔ s = P)
  have hpos {i : I} (hi : i ∈ P) : 0 < h i := (Finset.mem_filter.mp hi).2
  have hleft : (∑ i ∈ s, h i) ≤ ∑ i ∈ s ∩ P, h i := by
    apply Finset.sum_le_sum_of_subset_of_nonpos Finset.inter_subset_left
    intro i his hin
    apply le_of_not_gt
    intro hp
    exact hin (Finset.mem_inter.mpr ⟨his, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩⟩)
  have hright : (∑ i ∈ s ∩ P, h i) ≤ ∑ i ∈ P, h i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ hi _ => (hpos hi).le)
  refine ⟨hleft.trans hright, ⟨?_, ?_⟩⟩
  · intro heq
    suffices hPS : P ⊆ s from (Finset.eq_of_subset_of_card_le hPS hc.le).symm
    intro i hiP
    by_contra his
    have hlt : (∑ j ∈ s ∩ P, h j) < ∑ j ∈ P, h j :=
      Finset.sum_lt_sum_of_subset Finset.inter_subset_right hiP
        (fun hm => his (Finset.mem_inter.mp hm).1) (hpos hiP)
        (fun _ hj _ => (hpos hj).le)
    have habs := hleft.trans_lt hlt
    rw [heq] at habs
    exact (lt_irrefl _) habs
  · intro hs
    rw [hs]

end FrobeniusSplitting
