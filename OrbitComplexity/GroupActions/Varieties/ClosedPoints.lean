import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace

/-! # Constructible sets and closed points

In a Jacobson space every nonempty constructible set contains a closed point. Consequently,
closed points determine constructible subsets.

## Main results

* `GroupActions.constructible_closedPoint`: nonempty constructible sets contain closed points.
* `GroupActions.constructible_eq`: constructible sets with the same closed points are equal.
-/

open Set Topology

namespace GroupActions

variable {X : Type*} [TopologicalSpace X] [JacobsonSpace X]

/-- Every nonempty constructible subset of a Jacobson space contains a closed point. -/
theorem constructible_closedPoint {S : Set X} (hS : IsConstructible S) (hne : S.Nonempty) :
    (S ∩ closedPoints X).Nonempty := by
  induction S, hS using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun U hU V hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun U hU V hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    exact nonempty_inter_closedPoints hne
      (hU.1.isLocallyClosed.inter hV.1.isClosed_compl.isLocallyClosed)
  | sup U _ V _ hU hV =>
    obtain hne | hne := Set.union_nonempty.mp hne
    · exact (hU hne).mono (Set.inter_subset_inter_left _ Set.subset_union_left)
    · exact (hV hne).mono (Set.inter_subset_inter_left _ Set.subset_union_right)

private theorem constructible_subset {S T : Set X} (hS : IsConstructible S)
    (hT : IsConstructible T) (hclosed : S ∩ closedPoints X ⊆ T) : S ⊆ T := by
  intro x hx
  by_contra hxt
  obtain ⟨p, hp, hpc⟩ := constructible_closedPoint (hS.sdiff hT) ⟨x, hx, hxt⟩
  exact hp.2 (hclosed ⟨hp.1, hpc⟩)

/-- Constructible subsets of a Jacobson space are determined by their closed points. -/
theorem constructible_eq {S T : Set X} (hS : IsConstructible S) (hT : IsConstructible T)
    (hclosed : S ∩ closedPoints X = T ∩ closedPoints X) : S = T := by
  apply Set.Subset.antisymm
  · apply constructible_subset hS hT
    rw [hclosed]
    exact Set.inter_subset_left
  · apply constructible_subset hT hS
    rw [← hclosed]
    exact Set.inter_subset_left

end GroupActions
