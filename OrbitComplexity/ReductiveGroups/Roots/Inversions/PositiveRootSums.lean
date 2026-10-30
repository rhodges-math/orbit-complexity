import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionsWords

/-!
# Ordering a prescribed multiset of positive root summands

Auxiliary height calculations take place in the integral root span.
They do not identify it with the full character lattice or assume that roots
span the ambient module over its scalar ring.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The sum of simple-root coordinates on the integral root span. -/
def rootLatticeHeight (b : P.Base) : P.rootSpan ℤ →ₗ[ℤ] ℤ :=
  b.toWeightBasisInt.sumCoords

/-- The equality is

```lean
rootLatticeHeight b (P.rootSpanMem ℤ i) = 1
```
-/
theorem rootLatticeHeight_simple (b : P.Base) (i : b.support) :
    rootLatticeHeight b (P.rootSpanMem ℤ i) = 1 := by
  have he : P.rootSpanMem ℤ i = b.toWeightBasisInt i := by
    apply Subtype.ext
    simp
  rw [he]
  exact b.toWeightBasisInt.sumCoords_self_apply i

/-- The additive lattice height agrees with Mathlib's root height. -/
@[simp] theorem rootLatticeHeight_root (b : P.Base) (i : ι) :
    rootLatticeHeight b (P.rootSpanMem ℤ i) = b.height i := by
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int i
  have he : P.rootSpanMem ℤ i = ∑ j ∈ b.support, f j • P.rootSpanMem ℤ j := by
    apply Subtype.ext
    simpa using hf
  rw [he, map_sum, b.height_eq_sum hf]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, rootLatticeHeight_simple b ⟨j, hj⟩]
  simp

omit [CharZero R] in
/-- The equality is

```lean
(l.map (P.rootSpanMem ℤ)).sum = P.rootSpanMem ℤ i
```
-/
theorem rootLattice_sum_eq_of_root_sum_eq (l : List ι) (i : ι)
    (h : (l.map P.root).sum = P.root i) :
    (l.map (P.rootSpanMem ℤ)).sum = P.rootSpanMem ℤ i := by
  apply Subtype.ext
  simpa [Function.comp_def] using h

/-- The equality is

```lean
(l.map b.height).sum = b.height i
```
-/
theorem height_eq_sum_of_root_sum_eq (b : P.Base) (l : List ι) (i : ι)
    (h : (l.map P.root).sum = P.root i) : (l.map b.height).sum = b.height i := by
  have he := congrArg (rootLatticeHeight b) (rootLattice_sum_eq_of_root_sum_eq l i h)
  simpa only [map_list_sum, List.map_map, Function.comp_def, rootLatticeHeight_root] using he

/-- For these parameters,

```lean
0 < (l.map b.height).sum
```
-/
theorem sum_heights_pos (b : P.Base) (l : List ι) (hne : l ≠ [])
    (hpos : ∀ i ∈ l, b.IsPos i) : 0 < (l.map b.height).sum := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hi : 0 < b.height i := hpos i (by simp)
    by_cases hl : l = []
    · simpa [hl] using hi
    · exact add_pos hi (ih hl (fun j hj => hpos j (List.mem_cons_of_mem i hj)))

/-- For these parameters,

```lean
(l.map P.root).sum ≠ 0
```
-/
theorem root_sum_ne_zero_of_positive (b : P.Base) (l : List ι) (hne : l ≠ [])
    (hpos : ∀ i ∈ l, b.IsPos i) : (l.map P.root).sum ≠ 0 := by
  intro hzero
  have he : (l.map (P.rootSpanMem ℤ)).sum = 0 := by
    apply Subtype.ext
    simpa [Function.comp_def] using hzero
  have hh := congrArg (rootLatticeHeight b) he
  simp only [map_list_sum, List.map_map, Function.comp_def, rootLatticeHeight_root,
    map_zero] at hh
  exact (ne_of_gt (sum_heights_pos b l hne hpos)) hh

/-- For these parameters,

```lean
b.IsPos i
```
-/
theorem isPos_of_positive_root_sum (b : P.Base) (l : List ι) (i : ι)
    (hpos : ∀ j ∈ l, b.IsPos j) (h : (l.map P.root).sum = P.root i) : b.IsPos i := by
  have hne : l ≠ [] := by
    intro he
    exact P.ne_zero i (by simpa [he] using h.symm)
  change 0 < b.height i
  rw [← height_eq_sum_of_root_sum_eq b l i h]
  exact sum_heights_pos b l hne hpos

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

omit [IsDomain R] [P.IsReduced] in
/-- The pairings of the prescribed summands against the total coroot sum
to two, so at least one summand pairs positively with the total root. -/
theorem exists_mem_pairingIn_pos_of_root_sum_eq (l : List ι) (i : ι)
    (h : (l.map P.root).sum = P.root i) : ∃ j ∈ l, 0 < P.pairingIn ℤ i j := by
  have he := congrArg (P.coroot'In ℤ i) (rootLattice_sum_eq_of_root_sum_eq l i h)
  have hsum : (l.map (fun j => P.pairingIn ℤ j i)).sum = 2 := by
    simpa only [map_list_sum, List.map_map, Function.comp_def,
      RootPairing.coroot'In_rootSpanMem_eq_pairingIn, RootPairing.pairingIn_same] using he
  by_contra! hn
  have aux : ∀ t : List ι, (∀ j ∈ t, P.pairingIn ℤ j i ≤ 0) →
      (t.map (fun j => P.pairingIn ℤ j i)).sum ≤ 0 := by
    intro t ht
    induction t with
    | nil => simp
    | cons j t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonpos (ht j (by simp))
        (ih (fun k hk => ht k (List.mem_cons_of_mem j hk)))
  have hnonpos : (l.map (fun j => P.pairingIn ℤ j i)).sum ≤ 0 := by
    apply aux
    intro j hj
    exact le_of_not_gt (fun hpos => not_lt_of_ge (hn j hj)
      ((P.zero_lt_pairingIn_iff' ℤ).mp hpos))
  omega

omit [P.IsReduced] in
/-- A prescribed list of positive roots summing to a root can be permuted
so that every nonempty partial sum is a root. Repetitions are retained. -/
theorem exists_perm_root_partial_sums (b : P.Base) (l : List ι) (i : ι)
    (hpos : ∀ j ∈ l, b.IsPos j) (hsum : (l.map P.root).sum = P.root i) :
    ∃ v : List ι, v.Perm l ∧
      ∀ n : ℕ, 0 < n → n ≤ v.length → ((v.take n).map P.root).sum ∈ Set.range P.root := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing l i with | _ _ ih
  subst hn
  have hne : l ≠ [] := by
    intro he
    exact P.ne_zero i (by simpa [he] using hsum.symm)
  by_cases hlen : l.length = 1
  · obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨[j], List.Perm.refl _, ?_⟩
    intro n hn hn'
    have he : n = 1 := by simp only [List.length_singleton] at hn'; omega
    subst n
    simp
  obtain ⟨j, hj, hpair⟩ := exists_mem_pairingIn_pos_of_root_sum_eq l i hsum
  have hlength := List.length_erase_add_one hj
  have hrestne : l.erase j ≠ [] := by
    intro he
    simp only [he, List.length_nil] at hlength
    omega
  have hrestpos : ∀ k ∈ l.erase j, b.IsPos k :=
    fun k hk => hpos k (List.mem_of_mem_erase hk)
  have hrestsum : P.root j + ((l.erase j).map P.root).sum = P.root i :=
    (List.sum_map_erase P.root hj).trans hsum
  have hij : i ≠ j := by
    intro he
    have hzero : ((l.erase j).map P.root).sum = 0 := by
      simpa only [he, add_eq_left] using hrestsum
    exact root_sum_ne_zero_of_positive b _ hrestne hrestpos hzero
  obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair hij
  have hkSum : ((l.erase j).map P.root).sum = P.root k := by
    rw [hk, ← hrestsum, add_sub_cancel_left]
  obtain ⟨v, hv, hpartial⟩ := ih (l.erase j).length (by omega) (l.erase j) k hrestpos hkSum rfl
  refine ⟨v ++ [j], ?_, ?_⟩
  · exact (hv.append_right [j]).trans
      (List.perm_append_comm.trans (List.perm_cons_erase hj).symm)
  · intro n hn hn'
    by_cases hnv : n ≤ v.length
    · rw [List.take_append_of_le_length hnv]
      exact hpartial n hn hnv
    · have hnEq : n = (v ++ [j]).length := by
        simp only [List.length_append, List.length_singleton] at hn' ⊢
        omega
      rw [hnEq, List.take_length]
      refine ⟨i, ?_⟩
      have he := (hv.map P.root).sum_eq
      simpa only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
        he, add_comm] using hrestsum.symm

omit [P.IsReduced] in
/-- The same prescribed ordering has positive root partial sums, since
every term is positive and additive lattice height is strictly positive. -/
theorem exists_perm_positive_root_partial_sums (b : P.Base) (l : List ι) (i : ι)
    (hpos : ∀ j ∈ l, b.IsPos j) (hsum : (l.map P.root).sum = P.root i) :
    ∃ v : List ι, v.Perm l ∧ ∀ n : ℕ, 0 < n → n ≤ v.length →
      ∃ j : ι, b.IsPos j ∧ P.root j = ((v.take n).map P.root).sum := by
  obtain ⟨v, hv, hpartial⟩ := exists_perm_root_partial_sums b l i hpos hsum
  refine ⟨v, hv, ?_⟩
  intro n hn hn'
  obtain ⟨j, hj⟩ := hpartial n hn hn'
  refine ⟨j, isPos_of_positive_root_sum b (v.take n) j ?_ hj.symm, hj⟩
  intro k hk
  exact hpos k (hv.mem_iff.mp (List.mem_of_mem_take hk))

end ReductiveGroups
