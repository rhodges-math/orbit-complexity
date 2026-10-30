import OrbitComplexity.BruhatIntervals.Permutations.Words
import OrbitComplexity.BruhatIntervals.Order.Ranks

/-!
# Finite permutation intervals and their top labels

Subword products of a computed reduced word enumerate every lower interval. Filtering these
products by the lower bound gives a finite interval whose rank sizes and top-cover pairs are
computed with the ordinary inversion count.

## Main results

* `TypeA.mem_intervalElements`: the finite enumeration is the Bruhat interval.
* `TypeA.rankSize_eq_filter_card`: inversion-count filtering computes each rank size.
* `TypeA.topCoverLabels_eq`: top-cover labels are roots of the computed coordinate pairs.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5, 2.2 and 2.7.
-/

namespace BruhatIntervals.TypeA

/-- The products of all subwords of a computed reduced word enumerate its lower interval. -/
def subwordProducts (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    Finset (Equiv.Perm (Fin (n + 1))) :=
  ((reducedWord n w).sublists.map (wordPermutation n)).toFinset

/-- Membership among subword products is Bruhat comparison. -/
theorem mem_subwordProducts (n : ℕ) (u w : Equiv.Perm (Fin (n + 1))) :
    u ∈ subwordProducts n w ↔ (coxeterSystem n).BruhatLE u w := by
  simp only [subwordProducts, List.mem_toFinset, bruhatLE_iff_mem_subwords]

/-- Filtering a lower interval by another lower bound enumerates a permutation Bruhat interval. -/
def intervalElements (n : ℕ) (u v : Equiv.Perm (Fin (n + 1))) :
    Finset (Equiv.Perm (Fin (n + 1))) :=
  (subwordProducts n v).filter (fun w => u ∈ subwordProducts n w)

/-- The enumerated finite interval has exactly the vertices of the Bruhat interval. -/
theorem mem_intervalElements (n : ℕ) (u v w : Equiv.Perm (Fin (n + 1))) :
    w ∈ intervalElements n u v ↔ w ∈ bruhatInterval (coxeterSystem n) u v := by
  simp only [intervalElements, Finset.mem_filter, mem_subwordProducts, bruhatInterval,
    Set.mem_ofPred_eq, and_comm]

/-- A rank size is computed by filtering interval elements by their inversion counts. -/
theorem rankSize_eq_filter_card (n : ℕ) (u v : Equiv.Perm (Fin (n + 1))) (k : ℕ) :
    rankSize (coxeterSystem n) u v k =
      ((intervalElements n u v).filter (fun w =>
        (inversionPairs n w).card = (inversionPairs n u).card + k)).card := by
  unfold rankSize
  have heq : {w | w ∈ bruhatInterval (coxeterSystem n) u v ∧
      (coxeterSystem n).length w = (coxeterSystem n).length u + k} =
      (↑((intervalElements n u v).filter (fun w =>
        (inversionPairs n w).card = (inversionPairs n u).card + k)) :
          Set (Equiv.Perm (Fin (n + 1)))) := by
    ext w
    simp only [Finset.mem_coe, Finset.mem_filter, mem_intervalElements,
      length_eq_inversions, Set.mem_ofPred_eq]
  rw [heq, Set.ncard_coe_finset]

/-- The increasing coordinate pairs whose transpositions give top covers in an interval. -/
def topCoverPairs (n : ℕ) (u v : Equiv.Perm (Fin (n + 1))) :
    Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter (fun pair => pair.1 < pair.2 ∧
    Equiv.swap pair.1 pair.2 * v ∈ intervalElements n u v ∧
    (inversionPairs n v).card =
      (inversionPairs n (Equiv.swap pair.1 pair.2 * v)).card + 1)

/-- The labels of the top covers are the coordinate roots of the enumerated top-cover pairs. -/
theorem topCoverLabels_eq (n : ℕ) (u v : Equiv.Perm (Fin (n + 1))) :
    {α | ∃ x ∈ bruhatInterval (coxeterSystem n) u v,
      ∃ h : (bruhatGraph (coxeterSystem n)).Adj x v,
        (coxeterSystem n).length v = (coxeterSystem n).length x + 1 ∧
          edgeLabel (realization n) x v h = α} =
      (fun pair : Fin (n + 1) × Fin (n + 1) => root n pair.1 pair.2) ''
        (topCoverPairs n u v : Set (Fin (n + 1) × Fin (n + 1))) := by
  ext α
  constructor
  · rintro ⟨x, hx, h, hlength, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := (bruhatGraph_adj_iff_swap n v x).mp
      ((bruhatGraph (coxeterSystem n)).adj_symm h)
    refine ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_coe, topCoverPairs, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_intervalElements]
      exact ⟨hij, hx, by simpa only [length_eq_inversions] using hlength⟩
    · rw [edgeLabel_symm (realization n) _ _ h]
      exact (edgeLabel_swap n v i j hij _).symm
  · rintro ⟨⟨i, j⟩, hpair, rfl⟩
    obtain ⟨hij, hmem, hlength⟩ : i < j ∧
        Equiv.swap i j * v ∈ bruhatInterval (coxeterSystem n) u v ∧
        (coxeterSystem n).length v =
          (coxeterSystem n).length (Equiv.swap i j * v) + 1 := by
      simpa only [Finset.mem_coe, topCoverPairs, Finset.mem_filter, Finset.mem_univ,
        true_and, mem_intervalElements, length_eq_inversions] using hpair
    have hforward : (bruhatGraph (coxeterSystem n)).Adj v (Equiv.swap i j * v) := by
      change (coxeterSystem n).IsReflection (Equiv.swap i j * v * v⁻¹)
      simpa only [mul_inv_cancel_right] using swap_isReflection n i j (ne_of_lt hij)
    have hback := (bruhatGraph (coxeterSystem n)).adj_symm hforward
    refine ⟨Equiv.swap i j * v, hmem, hback, hlength, ?_⟩
    rw [edgeLabel_symm (realization n) _ _ hback]
    exact edgeLabel_swap n v i j hij _

end BruhatIntervals.TypeA
