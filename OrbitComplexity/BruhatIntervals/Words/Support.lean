import OrbitComplexity.BruhatIntervals.Order.Basic
import Mathlib.Data.Set.Card

/-!
# Support of a Coxeter group element

The support of an element is the set of simple reflections occurring in each of its reduced words.
It is finite and increases along the Bruhat order.

## Main definitions

* `support`: the set of simple reflections below an element in the Bruhat order.
* `supportCard`: the cardinality of the support.

## Main results

* `support_eq_letters`: every reduced word has exactly the support as its set of letters.
* `supportCard_le_length`: the support has cardinality at most the Coxeter length.
* `supportCard_eq_length_iff`: equality holds exactly when a reduced word has distinct letters.

## Implementation notes

Support is a set of elements of the Coxeter group, so its members are simple reflections rather than
indices for simple reflections. Words are mapped by `CoxeterSystem.simple` before comparing letters.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- The support of `w` is the set of simple reflections below `w` in the Bruhat order. -/
def support (w : W) : Set W := {t | (∃ i : S, cs.simple i = t) ∧ cs.BruhatLE t w}

/-- A simple reflection lies below the product of a reduced word exactly when it occurs in it. -/
theorem simple_bruhatLE_iff_mem {word : List S} (hred : cs.IsReduced word) (i : S) :
    cs.BruhatLE (cs.simple i) (cs.wordProd word) ↔ cs.simple i ∈ word.map cs.simple := by
  constructor
  · intro h
    obtain ⟨subword, hsub, hprod, hlen⟩ :=
      h.exists_sublist_wordProd_eq_length_eq word rfl
    rw [cs.length_simple] at hlen
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
    rw [cs.wordProd_singleton] at hprod
    exact List.mem_map.mpr ⟨j, hsub.subset (by simp), hprod⟩
  · intro h
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    rw [← hji, ← cs.wordProd_singleton]
    exact cs.bruhatLE_wordProd_of_sublist hred (List.singleton_sublist.mpr hj)

/-- Every reduced word for `w` has the support of `w` as its set of simple reflections. -/
theorem support_eq_letters {w : W} {word : List S} (hred : cs.IsReduced word)
    (hword : cs.wordProd word = w) :
    support cs w = {t | t ∈ word.map cs.simple} := by
  subst w
  ext t
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact (simple_bruhatLE_iff_mem cs hred i).mp h
  · intro ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact ⟨⟨i, rfl⟩, (simple_bruhatLE_iff_mem cs hred i).mpr
      (List.mem_map.mpr ⟨i, hi, rfl⟩)⟩

/-- The support of every Coxeter group element is finite. -/
theorem support_finite (w : W) : (support cs w).Finite := by
  obtain ⟨word, hred, hword⟩ := cs.exists_isReduced w
  rw [support_eq_letters cs hred hword.symm]
  exact List.finite_toSet _

/-- Support increases along the Bruhat order. -/
theorem support_mono {u w : W} (h : cs.BruhatLE u w) : support cs u ⊆ support cs w :=
  fun _ ht => ⟨ht.1, ht.2.trans h⟩

/-- The cardinality of the support of a Coxeter group element. -/
noncomputable def supportCard (w : W) : ℕ := (support cs w).ncard

/-- The cardinality of support increases along the Bruhat order. -/
theorem supportCard_mono {u w : W} (h : cs.BruhatLE u w) :
    supportCard cs u ≤ supportCard cs w :=
  Set.ncard_le_ncard (support_mono cs h) (support_finite cs w)

open scoped Classical in
/-- The support cardinality is the number of distinct simple reflections in any reduced word. -/
theorem supportCard_eq_card {w : W} {word : List S} (hred : cs.IsReduced word)
    (hword : cs.wordProd word = w) :
    supportCard cs w = (word.map cs.simple).toFinset.card := by
  rw [supportCard, support_eq_letters cs hred hword, ← List.coe_toFinset,
    Set.ncard_coe_finset]

/-- The support cardinality is at most the Coxeter length. -/
theorem supportCard_le_length (w : W) : supportCard cs w ≤ cs.length w := by
  classical
  obtain ⟨word, hred, hword⟩ := cs.exists_isReduced w
  rw [supportCard_eq_card cs hred hword.symm, hword, hred.eq]
  simpa only [List.length_map] using (word.map cs.simple).toFinset_card_le

/-- The support cardinality equals the length exactly when the letters of a reduced word are
pairwise distinct. -/
theorem supportCard_eq_length_iff {w : W} {word : List S} (hred : cs.IsReduced word)
    (hword : cs.wordProd word = w) :
    supportCard cs w = cs.length w ↔ (word.map cs.simple).Nodup := by
  classical
  rw [supportCard_eq_card cs hred hword, ← hword, hred.eq]
  simpa only [List.toFinset_coe, Multiset.coe_card, Multiset.coe_nodup, List.length_map] using
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (word.map cs.simple : Multiset W)))

end BruhatIntervals
