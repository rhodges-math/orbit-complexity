import OrbitComplexity.BruhatIntervals.Permutations.Bruhat
import OrbitComplexity.BruhatIntervals.Permutations.Length
import Mathlib.Data.List.Sublists

/-!
# Computable reduced permutation words

Repeatedly removing an adjacent descent constructs a reduced word for every permutation.
The inversion count supplies the initial recursion fuel. The subword property then turns
Bruhat comparison with that permutation into membership in a finite list of products.

## Main results

* `TypeA.reducedWord_spec`: the descent procedure gives a reduced word with the required product.
* `TypeA.bruhatLE_iff_mem_subwords`: subword products decide permutation Bruhat comparisons.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 2.2.
-/

namespace BruhatIntervals.TypeA

/-- A permutation word evaluates as the product of its adjacent coordinate transpositions. -/
def wordPermutation (n : ℕ) (word : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (word.map (simpleReflection n)).prod

/-- Evaluation in the permutation Coxeter system agrees with adjacent-transposition product. -/
theorem wordProd_eq_wordPermutation (n : ℕ) (word : List (Fin n)) :
    (coxeterSystem n).wordProd word = wordPermutation n word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [(coxeterSystem n).wordProd_cons, ih, coxeterSystem_simple]
    rfl

private def descentSet (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i.succ < w i.castSucc)

private def firstDescent (n : ℕ) (w : Equiv.Perm (Fin (n + 1)))
    (h : ∃ i : Fin n, w i.succ < w i.castSucc) : Fin n :=
  (descentSet n w).min' (by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

private theorem firstDescent_desc (n : ℕ) (w : Equiv.Perm (Fin (n + 1)))
    (h : ∃ i : Fin n, w i.succ < w i.castSucc) :
    (coxeterSystem n).IsRightDescent w (firstDescent n w h) := by
  apply (isRightDescent_iff n w _).mpr
  have hmem : firstDescent n w h ∈ descentSet n w := Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

private def reducedAux (n : ℕ) : ℕ → Equiv.Perm (Fin (n + 1)) → List (Fin n)
  | 0, _ => []
  | fuel + 1, w =>
    if h : ∃ i : Fin n, w i.succ < w i.castSucc then
      reducedAux n fuel (w * simpleReflection n (firstDescent n w h)) ++
        [firstDescent n w h]
    else []

private theorem reducedAux_spec (n fuel : ℕ) (w : Equiv.Perm (Fin (n + 1)))
    (hbound : (coxeterSystem n).length w ≤ fuel) :
    (coxeterSystem n).IsReduced (reducedAux n fuel w) ∧
      (coxeterSystem n).wordProd (reducedAux n fuel w) = w := by
  induction fuel generalizing w with
  | zero =>
    have hw : w = 1 := (coxeterSystem n).length_eq_zero_iff.mp (by omega)
    subst w
    exact ⟨(coxeterSystem n).length_one, (coxeterSystem n).wordProd_nil⟩
  | succ fuel ih =>
    rw [reducedAux]
    split_ifs with h
    · let i := firstDescent n w h
      have hdesc := firstDescent_desc n w h
      have hlength := (coxeterSystem n).isRightDescent_iff.mp hdesc
      rw [coxeterSystem_simple] at hlength
      obtain ⟨hred, hprod⟩ := ih (w * simpleReflection n i) (by
        change (coxeterSystem n).length (w * simpleReflection n i) + 1 =
          (coxeterSystem n).length w at hlength
        omega)
      have hproduct : (coxeterSystem n).wordProd
          (reducedAux n fuel (w * simpleReflection n i) ++ [i]) = w := by
        rw [(coxeterSystem n).wordProd_append, (coxeterSystem n).wordProd_singleton,
          hprod, ← coxeterSystem_simple]
        exact (coxeterSystem n).simple_mul_simple_cancel_right i
      refine ⟨?_, hproduct⟩
      rw [CoxeterSystem.IsReduced, hproduct, List.length_append, List.length_singleton,
        ← hred.eq, hprod]
      exact hlength.symm
    · have hw : w = 1 := by
        by_contra hne
        obtain ⟨i, hi⟩ := (coxeterSystem n).exists_rightDescent_of_ne_one hne
        exact h ⟨i, (isRightDescent_iff n w i).mp hi⟩
      subst w
      exact ⟨(coxeterSystem n).length_one, (coxeterSystem n).wordProd_nil⟩

/-- Removing the first available adjacent descent gives a computable reduced word. -/
def reducedWord (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) : List (Fin n) :=
  reducedAux n (inversionPairs n w).card w

/-- The computed word is reduced and evaluates to its input permutation. -/
theorem reducedWord_spec (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    (coxeterSystem n).IsReduced (reducedWord n w) ∧
      (coxeterSystem n).wordProd (reducedWord n w) = w := by
  exact reducedAux_spec n _ w (le_of_eq (length_eq_inversions n w))

/-- Bruhat comparison is membership among the products of the computed reduced word's subwords. -/
theorem bruhatLE_iff_mem_subwords (n : ℕ) (u w : Equiv.Perm (Fin (n + 1))) :
    (coxeterSystem n).BruhatLE u w ↔
      u ∈ ((reducedWord n w).sublists.map (wordPermutation n)) := by
  rw [subword_property (coxeterSystem n) (reducedWord_spec n w).1
    (reducedWord_spec n w).2]
  simp only [List.mem_map, List.mem_sublists, wordProd_eq_wordPermutation]

end BruhatIntervals.TypeA
