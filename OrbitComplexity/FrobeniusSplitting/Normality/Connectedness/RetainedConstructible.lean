import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible
import Mathlib.Topology.Sober

/-! # Removing constructible exceptional sets by one base localization

Constructible subsets missing the generic fibre of an integral coefficient base become
empty after a nonzero principal localization. Finitely many such conditions can use the
same localization, by taking the union of their constructible images in the base.
-/

namespace FrobeniusSplitting

open CategoryTheory AlgebraicGeometry Topology Set

universe u v

private theorem generic_decides_constructible {X : Type*} [TopologicalSpace X]
    {η : X} (hη : IsGenericPoint η Set.univ) {T : Set X} (hT : IsConstructible T) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ (U ⊆ T ∨ U ⊆ Tᶜ) := by
  classical
  induction hT using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    by_cases hηV : η ∈ V
    · exact ⟨V, hV, hηV, Or.inl Subset.rfl⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ η, Or.inr ?_⟩
      intro x _ hx
      exact hηV ((hη.mem_open_set_iff hV).mpr ⟨x, Set.mem_univ x, hx⟩)
  | union T _ V _ hT hV =>
    obtain ⟨U, hU, hηU, hUT | hUT⟩ := hT
    · exact ⟨U, hU, hηU, Or.inl (hUT.trans Set.subset_union_left)⟩
    obtain ⟨W, hW, hηW, hWV | hWV⟩ := hV
    · exact ⟨W, hW, hηW, Or.inl (hWV.trans Set.subset_union_right)⟩
    refine ⟨U ∩ W, hU.inter hW, ⟨hηU, hηW⟩, Or.inr ?_⟩
    intro x hx hmem
    exact hmem.elim (hUT hx.1) (hWV hx.2)
  | compl T _ hT =>
    obtain ⟨U, hU, hηU, hUT | hUT⟩ := hT
    · exact ⟨U, hU, hηU, Or.inr (by simpa only [compl_compl] using hUT)⟩
    · exact ⟨U, hU, hηU, Or.inl hUT⟩

end FrobeniusSplitting
