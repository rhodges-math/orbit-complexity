import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProperty

/-!
# Subword transport across braid moves

A proper subword of a rank-two braid block has an alternating expression
of strictly smaller length. Either orientation of that shorter word occurs
inside the opposite braid block. The full block is transported by the
braid identity. This proves transport of arbitrary subword products in an
unchanged prefix and suffix; reduced-sublist deletion supplies a reduced
transported witness when needed.
-/

noncomputable section

namespace ReductiveGroups

open CoxeterSystem

/-- Increasing the length of an alternating word with fixed final letter
preserves the shorter word as a sublist. -/
theorem alternatingWord_sublist_of_le {α : Type*} (i j : α) {n m : ℕ} (h : n ≤ m) :
    (alternatingWord i j n).Sublist (alternatingWord i j m) := by
  induction m, h using Nat.le_induction with
  | base => exact .refl _
  | succ m _ ih =>
    exact ih.trans (by rw [alternatingWord_succ']; exact List.sublist_cons_self _ _)

/-- Either alternating orientation of strictly smaller length is a
sublist of the given alternating word. -/
theorem alternatingWord_sublist_swap_of_lt {α : Type*} (i j : α) {n m : ℕ} (h : n < m) :
    (alternatingWord i j n).Sublist (alternatingWord j i m) := by
  cases m with
  | zero => omega
  | succ m =>
    exact (alternatingWord_sublist_of_le i j (by omega : n ≤ m)).trans
      (by rw [alternatingWord_succ, List.concat_eq_append]; exact List.sublist_append_left _ _)

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Every subword of one braid block has a same-product
subword in the opposite braid block.  -/
theorem subword_braidWord_transport (b : P.Base) (i j : b.support)
    (p : List b.support) (hp : p.Sublist (braidWord (simpleCoxeterMatrix b) i j)) :
    ∃ q : List b.support, q.Sublist (braidWord (simpleCoxeterMatrix b) j i) ∧
      simpleWeylWord b q = simpleWeylWord b p := by
  have hlen := hp.length_le
  simp only [length_alternatingWord] at hlen
  by_cases he : p.length = simpleCoxeterMatrix b i j
  · have hpfull : p = braidWord (simpleCoxeterMatrix b) i j :=
      hp.eq_of_length (by simpa only [length_alternatingWord] using he)
    exact ⟨braidWord (simpleCoxeterMatrix b) j i, .refl _,
      by rw [hpfull, simpleWeylWord_braidWord_eq b i j]⟩
  · have hlt : p.length < simpleCoxeterMatrix b i j := by omega
    obtain ⟨n, hn, hprod⟩ := simpleWeylWord_two_letters_alternating b i j p
      (fun k hk => mem_alternatingWord_two_letters b i j _ (hp.subset hk))
    have hnm : n < simpleCoxeterMatrix b j i := by
      rw [(simpleCoxeterMatrix b).symmetric j i]
      omega
    rcases hprod with hprod | hprod
    · exact ⟨alternatingWord i j n, alternatingWord_sublist_swap_of_lt i j hnm, hprod.symm⟩
    · exact ⟨alternatingWord j i n, alternatingWord_sublist_of_le j i hnm.le, hprod.symm⟩

/-- A contextual braid move preserves every subword product. -/
theorem WeylBraidMove.subword_transport {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) {p : List b.support} (hp : p.Sublist l) :
    ∃ q : List b.support, q.Sublist k ∧ simpleWeylWord b q = simpleWeylWord b p := by
  obtain ⟨pre, post, i, j, _, rfl, rfl⟩ := h
  obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := List.sublist_append_iff.mp hp
  obtain ⟨p₀, pm, rfl, hp₀, hpm⟩ := List.sublist_append_iff.mp hp₁
  obtain ⟨qm, hqm, hprod⟩ := subword_braidWord_transport b i j pm hpm
  refine ⟨(p₀ ++ qm) ++ p₂, (hp₀.append hqm).append hp₂, ?_⟩
  simp only [simpleWeylWord_append, hprod]

/-- A finite chain of braid moves preserves every subword product. -/
theorem WeylBraidChain.subword_transport {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) {p : List b.support} (hp : p.Sublist l) :
    ∃ q : List b.support, q.Sublist k ∧ simpleWeylWord b q = simpleWeylWord b p := by
  induction h with
  | refl => exact ⟨p, hp, rfl⟩
  | tail _ hmove ih =>
    obtain ⟨q, hq, hprod⟩ := ih
    obtain ⟨r, hr, hprod'⟩ := hmove.subword_transport hq
    exact ⟨r, hr, hprod'.trans hprod⟩

/-- Reduced witnesses can be transported along the chain and then reduced
inside the target word by deletion. -/
theorem WeylBraidChain.reduced_subword_transport {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) {p : List b.support} (hp : p.Sublist l) :
    ∃ q : List b.support, q.Sublist k ∧ simpleWeylWord b q = simpleWeylWord b p ∧
      rootInversionCount b (simpleWeylWord b q) = q.length := by
  obtain ⟨q, hq, hprod⟩ := h.subword_transport hp
  obtain ⟨r, hr, hprod', hlen⟩ := simpleWeylWord_has_reduced_sublist b q
  exact ⟨r, hr.trans hq, hprod'.trans hprod, by rw [hprod', hlen]⟩

/-- A subword product transports from a fixed expression to
any other reduced expression of the same Weyl element. -/
theorem reduced_subword_transport_of_word_eq (b : P.Base) (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k)
    {p : List b.support} (hp : p.Sublist l) :
    ∃ q : List b.support, q.Sublist k ∧ simpleWeylWord b q = simpleWeylWord b p ∧
      rootInversionCount b (simpleWeylWord b q) = q.length :=
  (weylBraidChain_of_reduced b l k hl hk heq).reduced_subword_transport hp

end ReductiveGroups
