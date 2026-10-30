import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# Reduced expressions of reflections

Reflection inversions give reduced palindromic conjugate expressions. Every nonsimple
reflection can therefore be shortened by conjugation with a simple reflection.

## Main results

* `reflection_reduced_conj`: a reflection has a reduced palindromic expression.
* `reflection_simple_or_shorter`: simple conjugation shortens a nonsimple reflection.

## References

* M. Dyer, *Reflection Subgroups of Coxeter Systems*, Journal of Algebra 135 (1990),
  Section 2.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- Every reflection has a conjugate expression whose palindromic word is reduced. -/
theorem reflection_reduced_conj {t : W} (ht : cs.IsReflection t) :
    ∃ (initial : List Index) (i : Index),
      cs.IsReduced (initial ++ [i] ++ initial.reverse) ∧
        t = cs.wordProd initial * cs.simple i * (cs.wordProd initial)⁻¹ := by
  obtain ⟨word, hred, hprod⟩ := cs.exists_isReduced t
  have hinv : cs.IsLeftInversion (cs.wordProd word) t := by
    rw [← hprod]
    refine ⟨ht, ?_⟩
    rw [ht.mul_self, cs.length_one]
    exact ht.odd_length.pos
  have hmem := cs.mem_leftInvSeq_of_isLeftInversion word hinv
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
  have hjlen : j < word.length := by simpa only [cs.length_leftInvSeq] using hj
  have hconj : t = cs.wordProd (word.take j) * cs.simple word[j] *
      (cs.wordProd (word.take j))⁻¹ :=
    heq.symm.trans (cs.getElem_leftInvSeq word j hjlen)
  have hsplit : word.take j ++ [word[j]] ++ word.drop (j + 1) = word := by
    rw [List.take_concat_get' word j hjlen, List.take_append_drop]
  have hsplitprod := congrArg cs.wordProd hsplit
  simp only [cs.wordProd_append, cs.wordProd_singleton, ← hprod] at hsplitprod
  have hsuffix : cs.wordProd (word.drop (j + 1)) = (cs.wordProd (word.take j))⁻¹ := by
    apply mul_left_cancel (a := cs.wordProd (word.take j) * cs.simple word[j])
    exact hsplitprod.trans hconj
  have hsufflen : word.length - (j + 1) = j := by
    have h := congrArg cs.length hsuffix
    rw [(hred.drop (j + 1)).eq, cs.length_inv, (hred.take j).eq,
      List.length_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlen)] at h
    exact h
  have hlength : word.length = 2 * j + 1 := by omega
  have hnewprod : cs.wordProd (word.take j ++ [word[j]] ++ (word.take j).reverse) = t := by
    rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_singleton, cs.wordProd_reverse]
    exact hconj.symm
  refine ⟨word.take j, word[j], ?_, hconj⟩
  change cs.length (cs.wordProd (word.take j ++ [word[j]] ++ (word.take j).reverse)) =
    (word.take j ++ [word[j]] ++ (word.take j).reverse).length
  rw [hnewprod, hprod, hred.eq]
  simp only [List.length_append, List.length_singleton, List.length_reverse, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hjlen)]
  omega

/-- A reflection is simple, or some simple conjugation lowers its length by two. -/
theorem reflection_simple_or_shorter {t : W} (ht : cs.IsReflection t) :
    (∃ i : Index, t = cs.simple i) ∨
      ∃ i : Index, cs.length (cs.simple i * t * cs.simple i) + 2 = cs.length t := by
  obtain ⟨initial, i, hred, hconj⟩ := reflection_reduced_conj cs ht
  cases initial with
  | nil =>
    left
    exact ⟨i, by simpa only [cs.wordProd_nil, one_mul, inv_one, mul_one] using hconj⟩
  | cons j initial =>
    let middle := initial ++ [i] ++ initial.reverse
    have hred' : cs.IsReduced (j :: (middle ++ [j])) := by
      simpa only [middle, List.cons_append, List.reverse_cons, List.append_assoc] using hred
    have hmiddle : cs.IsReduced middle := by
      simpa only [List.drop_succ_cons, List.drop_zero, List.take_left] using
        ((hred'.drop 1).take middle.length)
    have hmiddleprod : cs.wordProd middle =
        cs.wordProd initial * cs.simple i * (cs.wordProd initial)⁻¹ := by
      dsimp only [middle]
      rw [cs.wordProd_append, cs.wordProd_append, cs.wordProd_singleton, cs.wordProd_reverse]
    have hpalprod : cs.wordProd (j :: (middle ++ [j])) = t := by
      rw [cs.wordProd_cons, cs.wordProd_append, cs.wordProd_singleton, hmiddleprod, hconj,
        cs.wordProd_cons, mul_inv_rev, cs.inv_simple]
      group
    have hshort : cs.simple j * t * cs.simple j = cs.wordProd middle := by
      rw [hconj, cs.wordProd_cons, mul_inv_rev, cs.inv_simple, hmiddleprod]
      group
      simp only [cs.simple_mul_simple_self, one_mul, cs.simple_mul_simple_cancel_right]
    right
    refine ⟨j, ?_⟩
    have hlength := hred'.eq
    rw [hpalprod] at hlength
    simp only [List.length_cons, List.length_append, List.length_nil] at hlength
    rw [hshort, hmiddle.eq]
    omega

end BruhatIntervals
