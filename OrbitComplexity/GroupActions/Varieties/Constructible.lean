import Mathlib.Topology.Constructible
import Mathlib.Topology.Irreducible

/-! # Dense constructible sets

A dense constructible subset of a nonempty topological space contains a nonempty open
subset. This is the topological step that supplies an open subset in the closure of an
algebraic group orbit.

## Main results

* `GroupActions.exists_open_subset`: dense constructible sets contain nonempty open subsets.

## References

* M. Brion, *Introduction to actions of algebraic groups*, Luminy lecture notes (2009),
  Proposition 1.11.
-/

open Set Topology

namespace GroupActions

variable {X : Type*} [TopologicalSpace X]

private theorem open_subset_or_compl {S : Set X} (hS : IsConstructible S) :
    ∀ W : Set X, IsOpen W → W.Nonempty →
      ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ W ∧ (U ⊆ S ∨ U ⊆ Sᶜ) := by
  induction hS using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    intro W hW hWne
    by_cases hne : (W ∩ V).Nonempty
    · exact ⟨W ∩ V, hW.inter hV, hne, inter_subset_left, Or.inl inter_subset_right⟩
    · refine ⟨W, hW, hWne, Set.Subset.rfl, Or.inr ?_⟩
      intro x hxW hxV
      exact hne ⟨x, hxW, hxV⟩
  | union S _ T _ hS hT =>
    intro W hW hWne
    obtain ⟨U, hU, hUne, hUW, hUS | hUS⟩ := hS W hW hWne
    · exact ⟨U, hU, hUne, hUW, Or.inl (hUS.trans Set.subset_union_left)⟩
    obtain ⟨V, hV, hVne, hVU, hVT | hVT⟩ := hT U hU hUne
    · exact ⟨V, hV, hVne, hVU.trans hUW, Or.inl (hVT.trans Set.subset_union_right)⟩
    refine ⟨V, hV, hVne, hVU.trans hUW, Or.inr ?_⟩
    intro x hx hmem
    exact hmem.elim (hUS (hVU hx)) (hVT hx)
  | compl S _ hS =>
    intro W hW hWne
    obtain ⟨U, hU, hUne, hUW, hUS | hUS⟩ := hS W hW hWne
    · exact ⟨U, hU, hUne, hUW, Or.inr (by simpa only [compl_compl] using hUS)⟩
    · exact ⟨U, hU, hUne, hUW, Or.inl hUS⟩

/-- A dense constructible set in a nonempty space contains a nonempty open subset. -/
theorem exists_open_subset [Nonempty X] {S : Set X}
    (hS : IsConstructible S) (hdense : Dense S) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  obtain ⟨U, hU, hne, -, hUS | hUS⟩ :=
    open_subset_or_compl hS Set.univ isOpen_univ Set.univ_nonempty
  · exact ⟨U, hU, hne, hUS⟩
  · obtain ⟨x, hxS, hxU⟩ := hdense.exists_mem_open hU hne
    exact (hUS hxU hxS).elim

end GroupActions
