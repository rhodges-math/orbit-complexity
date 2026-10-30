import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProperty

/-!
# Every reduced word of a Boolean element has distinct letters

The proof follows the Word Property argument. An alternating
word of length at least three repeats its first letter. Hence a braid move
out of a word with distinct letters must have length two, so it is a
commutation and preserves distinctness. Iterate along the proved
braid chain. Booleanity retains its existential reduced-word meaning.
-/

noncomputable section

namespace ReductiveGroups

/-- An alternating word with distinct letters has length at most two. -/
theorem alternatingWord_length_le_two_of_nodup {B : Type*} (i j : B) (n : ℕ)
    (h : (CoxeterSystem.alternatingWord i j n).Nodup) : n ≤ 2 := by
  by_contra hn
  have h0 : 0 < (CoxeterSystem.alternatingWord i j n).length := by
    rw [CoxeterSystem.length_alternatingWord]
    omega
  have h2 : 2 < (CoxeterSystem.alternatingWord i j n).length := by
    rw [CoxeterSystem.length_alternatingWord]
    omega
  have he : (CoxeterSystem.alternatingWord i j n)[0]'h0 =
      (CoxeterSystem.alternatingWord i j n)[2]'h2 := by
    rw [CoxeterSystem.getElem_alternatingWord i j n 0 (by omega),
      CoxeterSystem.getElem_alternatingWord i j n 2 (by omega)]
    simp [Nat.even_add]
  have he' : (0 : ℕ) = 2 := h.getElem_inj_iff.mp he
  omega

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- A braid move from a distinct-letter word is a commutation:
the matrix entry is two and the replaced blocks are `[i,j]` and `[j,i]`. -/
theorem WeylBraidMove.commutation_of_nodup {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) (hl : l.Nodup) :
    ∃ (pre post : List b.support) (i j : b.support),
      simpleCoxeterMatrix b i j = 2 ∧
      l = pre ++ [i, j] ++ post ∧ k = pre ++ [j, i] ++ post := by
  obtain ⟨pre, post, i, j, hij, rfl, rfl⟩ := h
  have hb := (List.nodup_append.mp (List.nodup_append.mp hl).1).2.1
  have hle := alternatingWord_length_le_two_of_nodup i j (simpleCoxeterMatrix b i j) hb
  have hge := simpleCoxeterMatrix_two_le b hij
  have hm : simpleCoxeterMatrix b i j = 2 := by omega
  have hm' : simpleCoxeterMatrix b j i = 2 :=
    ((simpleCoxeterMatrix b).symmetric j i).trans hm
  exact ⟨pre, post, i, j, hm,
    by change pre ++ CoxeterSystem.alternatingWord i j (simpleCoxeterMatrix b i j) ++ post = _
       rw [hm]; rfl,
    by change pre ++ CoxeterSystem.alternatingWord j i (simpleCoxeterMatrix b j i) ++ post = _
       rw [hm']; rfl⟩

/-- For these parameters,

```lean
l.Perm k
```
-/
theorem WeylBraidMove.perm_of_nodup {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) (hl : l.Nodup) : l.Perm k := by
  obtain ⟨pre, post, i, j, _, rfl, rfl⟩ := h.commutation_of_nodup hl
  exact ((List.Perm.refl pre).append (List.Perm.swap j i [])).append_right post

/-- Along a braid chain starting at a distinct-letter word, only
commutations occur, so even the multiset of letters is preserved. -/
theorem WeylBraidChain.perm_of_nodup {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) (hl : l.Nodup) : l.Perm k := by
  induction h with
  | refl => exact .refl _
  | tail _ hmove ih => exact ih.trans (hmove.perm_of_nodup (ih.nodup_iff.mp hl))

/-- For these parameters,

```lean
k.Nodup
```
-/
theorem WeylBraidChain.nodup {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) (hl : l.Nodup) : k.Nodup :=
  (h.perm_of_nodup hl).nodup_iff.mp hl

/-- Distinctness of a reduced expression is independent of the chosen reduced expression. -/
theorem nodup_of_reduced_word_eq (b : P.Base) (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k) (hnodup : l.Nodup) : k.Nodup :=
  (weylBraidChain_of_reduced b l k hl hk heq).nodup hnodup

/-- the existential Boolean condition is equivalent
to distinctness of every reduced expression in the constructed
Coxeter system. No new definition of Booleanity is imposed. -/
theorem weyl_boolean_iff_all_reduced_nodup (b : P.Base) (w : P.weylGroup) :
    (∃ l : List b.support, (weylCoxeterSystem b).IsReduced l ∧
      (weylCoxeterSystem b).wordProd l = w ∧ l.Nodup) ↔
    (∀ l : List b.support, (weylCoxeterSystem b).IsReduced l →
      (weylCoxeterSystem b).wordProd l = w → l.Nodup) := by
  constructor
  · rintro ⟨l, hl, hlw, hnodup⟩ k hk hkw
    exact (weylCoxeterSystem_word_property b l k hl hk
      (hlw.trans hkw.symm)).nodup hnodup
  · intro h
    obtain ⟨l, hl, hw⟩ := (weylCoxeterSystem b).exists_isReduced w
    exact ⟨l, hl, hw.symm, h l hl hw.symm⟩

end ReductiveGroups
