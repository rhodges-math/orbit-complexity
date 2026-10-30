import OrbitComplexity.BruhatIntervals.Permutations.PositiveRoots
import OrbitComplexity.BruhatIntervals.Graph.Basic

/-!
# Permutation roots and Bruhat edges

The reflection in a coordinate root swaps its two coordinates. Positive simple-root images
therefore identify right ascents with increasing adjacent values in one-line notation.

## Main results

* `TypeA.rootReflection_root`: coordinate-root reflection is a coordinate transposition.
* `TypeA.edgeLabel_swap`: the positive label of a transposition edge is its coordinate root.
* `TypeA.not_isRightDescent_iff`: adjacent increasing values characterize right ascents.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 2.1.
-/

namespace BruhatIntervals.TypeA

private theorem root_transport (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    ∃ k : Fin n, ∃ σ : Equiv.Perm (Fin (n + 1)), σ k.castSucc = i ∧ σ k.succ = j := by
  have hi : i.val < n := by
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  let k : Fin n := ⟨i.val, hi⟩
  have hki : k.castSucc = i := Fin.ext rfl
  have hfirst : i ≠ k.succ := by
    intro h
    have hval := congrArg Fin.val h
    change i.val = i.val + 1 at hval
    omega
  refine ⟨k, Equiv.swap k.succ j, ?_, Equiv.swap_apply_left _ _⟩
  rw [hki, Equiv.swap_apply_of_ne_of_ne hfirst (ne_of_lt hij)]

/-- Reflection in an increasing coordinate root interchanges its two coordinates. -/
theorem rootReflection_root (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    ((realization n).rootReflection
      ⟨root n i j, root_mem_positiveRoots n i j hij⟩).val = Equiv.swap i j := by
  obtain ⟨k, σ, hfirst, hlast⟩ := root_transport n i j hij
  have hroot : (realization n).action σ ((realization n).simpleRoot k) = root n i j := by
    change coordinateAction n σ (root n k.castSucc k.succ) = root n i j
    rw [coordinateAction_root, hfirst, hlast]
  have hpos : (realization n).action σ ((realization n).simpleRoot k) ∈
      (realization n).positiveRoots := hroot ▸ root_mem_positiveRoots n i j hij
  have hsub : (⟨root n i j, root_mem_positiveRoots n i j hij⟩ :
      {vector // vector ∈ (realization n).positiveRoots}) =
      ⟨(realization n).action σ ((realization n).simpleRoot k), hpos⟩ :=
    Subtype.ext hroot.symm
  rw [hsub, (realization n).rootReflection_translated_simple, coxeterSystem_simple]
  change σ * Equiv.swap k.castSucc k.succ * σ⁻¹ = Equiv.swap i j
  rw [← Equiv.swap_apply_apply, hfirst, hlast]

/-- Distinct coordinate transpositions are reflections of the permutation Coxeter system. -/
theorem swap_isReflection (n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j) :
    (coxeterSystem n).IsReflection (Equiv.swap i j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [← rootReflection_root n i j hlt]
    exact ((realization n).rootReflection
      ⟨root n i j, root_mem_positiveRoots n i j hlt⟩).property
  · rw [Equiv.swap_comm, ← rootReflection_root n j i hgt]
    exact ((realization n).rootReflection
      ⟨root n j i, root_mem_positiveRoots n j i hgt⟩).property

/-- A transposition edge has the increasing coordinate difference as its positive label. -/
theorem edgeLabel_swap (n : ℕ) (w : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : i < j)
    (h : (bruhatGraph (coxeterSystem n)).Adj w (Equiv.swap i j * w)) :
    edgeLabel (realization n) w (Equiv.swap i j * w) h = root n i j := by
  apply edgeLabel_unique (realization n) h
    ⟨root n i j, root_mem_positiveRoots n i j hij⟩
  rw [rootReflection_root n i j hij]

/-- Bruhat adjacency in the permutation group is multiplication by a coordinate transposition. -/
theorem bruhatGraph_adj_iff_swap (n : ℕ) (x y : Equiv.Perm (Fin (n + 1))) :
    (bruhatGraph (coxeterSystem n)).Adj x y ↔
      ∃ i j : Fin (n + 1), i < j ∧ y = Equiv.swap i j * x := by
  rw [bruhatGraph_adj_iff (realization n)]
  constructor
  · rintro ⟨vector, htarget⟩
    obtain ⟨i, j, hij, hroot⟩ := (Set.ext_iff.mp (positiveRoots_eq n) vector.val).mp
      vector.property
    have hsub : vector = ⟨root n i j, root_mem_positiveRoots n i j hij⟩ :=
      Subtype.ext hroot.symm
    refine ⟨i, j, hij, ?_⟩
    rwa [hsub, rootReflection_root] at htarget
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨⟨root n i j, root_mem_positiveRoots n i j hij⟩, ?_⟩
    rw [rootReflection_root n i j hij]

/-- A right ascent is an increase of adjacent permutation values. -/
theorem not_isRightDescent_iff (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    ¬ (coxeterSystem n).IsRightDescent w i ↔ w i.castSucc < w i.succ := by
  rw [← (realization n).action_simpleRoot_positive_iff]
  change coordinateAction n w (root n i.castSucc i.succ) ∈
    (realization n).positiveRoots ↔ _
  rw [coordinateAction_root, root_mem_positiveRoots_iff]

/-- A right descent is a decrease of adjacent permutation values. -/
theorem isRightDescent_iff (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (coxeterSystem n).IsRightDescent w i ↔ w i.succ < w i.castSucc := by
  have hne : w i.castSucc ≠ w i.succ := by
    intro h
    have hval := congrArg Fin.val (w.injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega
  rw [← not_iff_not, not_isRightDescent_iff]
  exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans (or_iff_left hne.symm)))

end BruhatIntervals.TypeA
