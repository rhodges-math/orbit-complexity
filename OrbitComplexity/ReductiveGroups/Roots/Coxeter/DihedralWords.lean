import OrbitComplexity.ReductiveGroups.Roots.Coxeter.FiniteWeyl
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationDeletion

/-!
# Two-generator words and finite product order

All words are Mathlib's `CoxeterSystem.alternatingWord`, evaluated by the
existing `simpleWeylWord`. The formal presentation is used only to
transport identities already proved there, never to infer injectivity.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

open CoxeterSystem

/-- Inversion count has the parity of every expression. -/
theorem RootInversionCount.simpleWeylWord_mod_two (b : P.Base) (l : List b.support) :
    rootInversionCount b (simpleWeylWord b l) % 2 = l.length % 2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l i ih =>
    simp only [simpleWeylWord_append, simpleWeylWord, mul_one,
      List.length_append, List.length_singleton]
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)
    · rw [rootInversionCount_mul_simple_of_pos b _ i hpos]
      omega
    · have hn := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) i
        ((root_height_neg_iff_not_isPos b _).mpr hpos)
      omega

/-- The equality is

```lean
simpleWeylWord b (alternatingWord i j n) =
      (if Even n then 1 else RootPairing.weylGroup.ofIdx P j) *
        (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j) ^ (n / 2)
```
-/
theorem SimpleWeylWord.alternatingWord_eq_mul_pow (b : P.Base) (i j : b.support) (n : ℕ) :
    simpleWeylWord b (alternatingWord i j n) =
      (if Even n then 1 else RootPairing.weylGroup.ofIdx P j) *
        (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j) ^ (n / 2) := by
  have h := congrArg (weylCoxeterPresentationMap b)
    ((simpleCoxeterMatrix b).toCoxeterSystem.prod_alternatingWord_eq_mul_pow i j n)
  by_cases hn : Even n <;>
    simpa only [weylCoxeterPresentationMap_wordProd, map_mul, map_pow, hn, ite_true, ite_false,
      map_one, CoxeterMatrix.toCoxeterSystem_simple, weylCoxeterPresentationMap_simple] using h

omit [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- A word using only two simple letters can be shortened by adjacent
cancellation to an alternating word of no greater length. -/
theorem simpleWeylWord_two_letters_alternating (b : P.Base) (i j : b.support)
    (l : List b.support) (hl : ∀ k ∈ l, k = i ∨ k = j) :
    ∃ n ≤ l.length,
      simpleWeylWord b l = simpleWeylWord b (alternatingWord i j n) ∨
      simpleWeylWord b l = simpleWeylWord b (alternatingWord j i n) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨0, le_rfl, Or.inl rfl⟩
  | append_singleton l k ih =>
    obtain ⟨n, hn, he⟩ := ih (fun x hx => hl x (List.mem_append_left _ hx))
    have hk := hl k (by simp)
    have same (u v : b.support) (he : simpleWeylWord b l =
        simpleWeylWord b (alternatingWord u v n)) :
        ∃ m ≤ (l ++ [v]).length,
          simpleWeylWord b (l ++ [v]) = simpleWeylWord b (alternatingWord u v m) ∨
          simpleWeylWord b (l ++ [v]) = simpleWeylWord b (alternatingWord v u m) := by
      cases n with
      | zero =>
        refine ⟨1, by simp, Or.inl ?_⟩
        simpa [simpleWeylWord_append, alternatingWord, simpleWeylWord] using he
      | succ n =>
        refine ⟨n, by simp only [List.length_append, List.length_singleton]; omega, Or.inr ?_⟩
        simpa only [simpleWeylWord_append, simpleWeylWord, mul_one, alternatingWord_succ,
          List.concat_eq_append, simpleWeylWord_append, simpleWeylWord, mul_one,
          mul_assoc, weylGroup_ofIdx_mul_self, mul_one] using
            congrArg (fun w => w * RootPairing.weylGroup.ofIdx P v) he
    have other (u v : b.support) (he : simpleWeylWord b l =
        simpleWeylWord b (alternatingWord u v n)) :
        simpleWeylWord b (l ++ [u]) = simpleWeylWord b (alternatingWord v u (n + 1)) := by
      simpa only [alternatingWord_succ, List.concat_eq_append, simpleWeylWord_append] using
        congrArg (fun w => w * simpleWeylWord b [u]) he
    rcases he with he | he <;> rcases hk with hk | hk
    · rw [hk]
      exact ⟨n + 1, by simp only [List.length_append, List.length_singleton]; omega,
        Or.inr (other i j he)⟩
    · rw [hk]
      exact same i j he
    · rw [hk]
      obtain ⟨m, hm, hprod⟩ := same j i he
      exact ⟨m, hm, hprod.symm⟩
    · rw [hk]
      exact ⟨n + 1, by simp only [List.length_append, List.length_singleton]; omega,
        Or.inl (other j i he)⟩

/-- Global reduction to a subword and adjacent cancellation give an alternating
expression whose length is the minimum, still using only the two letters. -/
theorem SimpleWeylWord.two_letters_minimal_alternating (b : P.Base) (i j : b.support)
    (l : List b.support) (hl : ∀ k ∈ l, k = i ∨ k = j) :
    simpleWeylWord b l = simpleWeylWord b
        (alternatingWord i j (rootInversionCount b (simpleWeylWord b l))) ∨
      simpleWeylWord b l = simpleWeylWord b
        (alternatingWord j i (rootInversionCount b (simpleWeylWord b l))) := by
  obtain ⟨v, hv, hprod, hlength⟩ := simpleWeylWord_has_reduced_sublist b l
  obtain ⟨n, hn, he⟩ := simpleWeylWord_two_letters_alternating b i j v
    (fun k hk => hl k (hv.subset hk))
  have n_eq (u v' : b.support)
      (he : simpleWeylWord b v = simpleWeylWord b (alternatingWord u v' n)) :
      n = rootInversionCount b (simpleWeylWord b l) := by
    have hle := RootInversionCount.simpleWeylWord_le_length b (alternatingWord u v' n)
    rw [← he, hprod, length_alternatingWord] at hle
    omega
  rcases he with he | he
  · exact Or.inl (hprod.symm.trans (by simpa only [n_eq i j he] using he))
  · exact Or.inr (hprod.symm.trans (by simpa only [n_eq j i he] using he))

end ReductiveGroups
