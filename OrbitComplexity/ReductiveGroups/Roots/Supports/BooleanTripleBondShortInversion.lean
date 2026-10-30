import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanTripleBondInversions

/-!
# Boolean Triple Bond Short Inversion

The short simple root itself occurs in the Boolean inversion set
when a non-multiplicity-free triple-bond inversion occurs. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- For these parameters,

```lean
P.root (q : ι) ∈ leftRootInversions b (simpleWeylWord b word)
```
-/
theorem LeftRootInversion.triple_bond_short_simple_mem
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    (β : ι) (hβ : P.root β ∈ leftRootInversions b (simpleWeylWord b word))
    (p q : b.support)
    (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1) :
    P.root (q : ι) ∈ leftRootInversions b (simpleWeylWord b word) := by
  have hpqne : p ≠ q := by
    intro h
    subst q
    rw [P.pairingIn_same] at hpq
    omega
  have hshape :=
    leftRootInversion_triple_bond_shape b word hword β hβ p q hp hq hpq hqp hbad
  have hβp : simpleRootCoeffInt b β p = 1 := by
    simpa [hpqne] using hshape.1 p
  have hβq : simpleRootCoeffInt b β q = 3 := by
    simpa [hpqne.symm] using hshape.1 q
  have hpWord : p ∈ word := LeftRootInversion.support_letter_mem_word
    b word hword β hβ p (by rw [hβp]; norm_num)
  have hqWord : q ∈ word := LeftRootInversion.support_letter_mem_word
    b word hword β hβ q (by rw [hβq]; norm_num)
  have hidxne : word.idxOf p ≠ word.idxOf q := by
    intro he
    exact hpqne ((List.idxOf_inj hpWord).mp he)
  have hqBefore : word.idxOf q < word.idxOf p := by
    rcases lt_or_gt_of_ne hidxne with h | h
    · have hbound := LeftRootInversion.bond_coefficient_lower_of_word_order
        b word hword β hβ p q hpqne (by rw [hβq]; norm_num) h
      rw [hβp, hβq, hqp] at hbound
      omega
    · exact h
  obtain ⟨L, T, hsplit⟩ := List.append_of_mem hqWord
  have hLnodup : L.Nodup := by
    rw [hsplit] at hword
    exact (List.nodup_append.mp hword).1
  have hqL : q ∉ L := by
    rw [hsplit] at hword
    intro h
    exact (List.nodup_append.mp hword).2.2 q h q (by simp) rfl
  have hidxq : word.idxOf q = L.length := by
    rw [hsplit, List.idxOf_append_of_notMem hqL]
    simp
  have hpL : p ∉ L := by
    intro h
    have hidxp : word.idxOf p = L.idxOf p := by
      rw [hsplit, List.idxOf_append_of_mem h]
    have hlt := List.idxOf_lt_length_of_mem h
    omega
  have hfixEach (j : b.support) (hj : j ∈ L) :
      P.reflection (j : ι) (P.root (q : ι)) = P.root (q : ι) := by
    have hjq : j ≠ q := fun he => hqL (he ▸ hj)
    have hjp : j ≠ p := fun he => hpL (he ▸ hj)
    have hnotAdj : ¬ (supportDynkinGraph b).Adj q j := by
      intro h
      exact tripleBond_no_neighbor_at_second b p q j hpqne
        hjp.symm hjq.symm hpq hqp h
    have hpair : P.pairingIn ℤ (q : ι) (j : ι) = 0 := by
      by_contra hn
      exact hnotAdj ((supportDynkinGraph_adj_iff b q j).mpr ⟨hjq.symm, hn⟩)
    rw [P.reflection_apply_root' ℤ, hpair]
    simp
  have hfix (K : List b.support) (hK : ∀ j ∈ K, j ∈ L) :
      simpleReflectionWord b K (P.root (q : ι)) = P.root (q : ι) := by
    induction K with
    | nil => simp [simpleReflectionWord]
    | cons j K ih =>
      have htail : ∀ k ∈ K, k ∈ L :=
        fun k hk => hK k (List.mem_cons_of_mem _ hk)
      simp only [simpleReflectionWord, LinearEquiv.mul_apply, ih htail]
      exact hfixEach j (hK j (by simp))
  have hroot := hfix L (fun j hj => hj)
  rw [LeftRootInversions.simpleWeylWord_eq_wordRootSet_ambient b word hword,
    hsplit, wordRootSet_append]
  exact Set.mem_union_right _ ⟨P.root (q : ι), by simp [wordRootSet], hroot⟩

end ReductiveGroups
