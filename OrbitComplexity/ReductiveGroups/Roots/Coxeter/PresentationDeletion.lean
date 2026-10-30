import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionLength

/-!
# Deletion and reduced subwords before presentation injectivity

The simple-root exchange theorem implies the Deletion Condition:
every nonminimal expression loses two specified letters without changing its
Weyl product. Iterating gives a reduced subword of every expression,
preserving its allowed simple letters.

These are statements in the Weyl group, not equalities in the formal
Coxeter presentation; completeness of its braid relations is
`weylCoxeterPresentationMap_injective` (`Roots/PresentationWordPropertyCoxeter.lean`).
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The Deletion Condition, with both removed positions made explicit. -/
theorem SimpleWeylWord.delete_two_of_count_lt_length (b : P.Base)
    (l : List b.support) (h : rootInversionCount b (simpleWeylWord b l) < l.length) :
    ∃ (pre mid post : List b.support) (i j : b.support),
      l = pre ++ [i] ++ mid ++ [j] ++ post ∧
      simpleWeylWord b l = simpleWeylWord b (pre ++ mid ++ post) ∧
      (pre ++ mid ++ post).length + 2 = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord] at h
  | append_singleton l j ih =>
    by_cases hred : rootInversionCount b (simpleWeylWord b l) = l.length
    · have hneg : b.height (P.weylGroupToPerm (simpleWeylWord b l) j) < 0 := by
        rw [root_height_neg_iff_not_isPos]
        intro hpos
        have hcount := rootInversionCount_mul_simple_of_pos b (simpleWeylWord b l) j hpos
        have hword : simpleWeylWord b (l ++ [j]) =
            simpleWeylWord b l * RootPairing.weylGroup.ofIdx P j := by
          simp [simpleWeylWord_append, simpleWeylWord]
        rw [hword, hcount, hred, List.length_append, List.length_singleton] at h
        exact (lt_irrefl _ h).elim
      obtain ⟨pre, i, mid, hword, _, hprod, hlength⟩ := simpleWeylWord_exchange b l j hneg
      refine ⟨pre, mid, [], i, j, ?_, ?_, ?_⟩
      · simp only [List.append_nil, hword]
      · simpa only [List.append_nil, simpleWeylWord_append, simpleWeylWord, mul_one] using hprod
      · simp only [List.append_nil, List.length_append, List.length_singleton] at hlength ⊢
        omega
    · have hlt : rootInversionCount b (simpleWeylWord b l) < l.length :=
        lt_of_le_of_ne (RootInversionCount.simpleWeylWord_le_length b l) hred
      obtain ⟨pre, mid, post, i, k, hword, hprod, hlength⟩ := ih hlt
      refine ⟨pre, mid, post ++ [j], i, k, ?_, ?_, ?_⟩
      · simp only [hword, List.append_assoc]
      · simpa only [simpleWeylWord_append, simpleWeylWord, mul_one, mul_assoc] using
          congrArg (fun w => w * RootPairing.weylGroup.ofIdx P j) hprod
      · simp only [List.length_append, List.length_singleton] at hlength ⊢
        omega

/-- A nonminimal expression has a product-equal sublist shorter by two. -/
theorem simpleWeylWord_has_shorter_sublist (b : P.Base) (l : List b.support)
    (h : rootInversionCount b (simpleWeylWord b l) < l.length) :
    ∃ m : List b.support, m.Sublist l ∧ simpleWeylWord b m = simpleWeylWord b l ∧
      m.length + 2 = l.length := by
  obtain ⟨pre, mid, post, i, j, hword, hprod, hlength⟩ :=
    SimpleWeylWord.delete_two_of_count_lt_length b l h
  refine ⟨pre ++ mid ++ post, ?_, hprod.symm, hlength⟩
  rw [hword]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    (List.Sublist.refl pre).append
      (List.Sublist.cons i ((List.Sublist.refl mid).append
        (List.Sublist.cons j (List.Sublist.refl post))))

/-- Every expression has a reduced subword with the same product.
Its letters remain a sublist of the prescribed expression. -/
theorem simpleWeylWord_has_reduced_sublist (b : P.Base) (l : List b.support) :
    ∃ m : List b.support, m.Sublist l ∧ simpleWeylWord b m = simpleWeylWord b l ∧
      m.length = rootInversionCount b (simpleWeylWord b l) := by
  have aux : ∀ n : ℕ, ∀ l : List b.support, l.length = n →
      ∃ m : List b.support, m.Sublist l ∧ simpleWeylWord b m = simpleWeylWord b l ∧
        m.length = rootInversionCount b (simpleWeylWord b l) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlength
      by_cases hred : rootInversionCount b (simpleWeylWord b l) = l.length
      · exact ⟨l, List.Sublist.refl _, rfl, hred.symm⟩
      · have hlt : rootInversionCount b (simpleWeylWord b l) < l.length :=
          lt_of_le_of_ne (RootInversionCount.simpleWeylWord_le_length b l) hred
        obtain ⟨m, hsub, hprod, hm⟩ := simpleWeylWord_has_shorter_sublist b l hlt
        obtain ⟨k, hk, hkprod, hklength⟩ := ih m.length (by omega) m rfl
        exact ⟨k, hk.trans hsub, hkprod.trans hprod, by simpa only [hprod] using hklength⟩
  exact aux l.length l rfl

/-- In particular, reduction preserves any prescribed allowed set of simple
letters. This applies to the two-generator words needed for the dihedral step. -/
theorem SimpleWeylWord.has_reduced_word_in_letters (b : P.Base)
    (J : Set b.support) (l : List b.support) (hl : ∀ i ∈ l, i ∈ J) :
    ∃ m : List b.support, (∀ i ∈ m, i ∈ J) ∧
      simpleWeylWord b m = simpleWeylWord b l ∧
      m.length = rootInversionCount b (simpleWeylWord b l) := by
  obtain ⟨m, hsub, hprod, hlength⟩ := simpleWeylWord_has_reduced_sublist b l
  exact ⟨m, fun i hi => hl i (hsub.subset hi), hprod, hlength⟩

end ReductiveGroups
