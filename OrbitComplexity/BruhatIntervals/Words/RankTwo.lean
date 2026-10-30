import OrbitComplexity.BruhatIntervals.Words.Alternating
import OrbitComplexity.BruhatIntervals.Graph.Basic

/-!
# Reflection parity in rank two

Reduced words on two simple indices alternate. Every alternating word of odd length is a
palindromic conjugate of a simple reflection, so the rank-two Bruhat graph joins exactly the
elements whose lengths have opposite parity.

## Main results

* `rankTwo_reflection_iff`: in rank two, reflections are exactly the odd-length elements.
* `rankTwo_adj_iff`: rank-two Bruhat adjacency is opposite length parity.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Example 1.2.
-/

namespace BruhatIntervals

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool} (cs : CoxeterSystem M W)

private theorem reduced_alternating {word : List Bool} (hred : cs.IsReduced word)
    (hne : word ≠ []) :
    ∃ i : Bool, word = CoxeterSystem.alternatingWord (!i) i word.length := by
  induction word using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton word i _ =>
    have hprefix : cs.IsReduced word := by simpa using hred.take word.length
    have hascent : ¬cs.IsRightDescent (cs.wordProd word) i := by
      rw [cs.not_isRightDescent_iff, hprefix.eq]
      simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton] using hred.eq
    have hletters (j : Bool) (_hj : j ∈ word) : j = i ∨ j = !i := by
      cases i <;> cases j <;> simp
    have heq := reduced_word_eq_alternating cs i (!i) hprefix hletters hascent
    refine ⟨i, ?_⟩
    rw [List.length_append, List.length_singleton, CoxeterSystem.alternatingWord_succ,
      List.concat_eq_append, ← heq]

private theorem alternating_odd_reflection (i j : Bool) (n : ℕ) :
    cs.IsReflection (cs.wordProd (CoxeterSystem.alternatingWord i j (2 * n + 1))) := by
  induction n generalizing i j with
  | zero => simpa only [Nat.mul_zero, zero_add, CoxeterSystem.alternatingWord,
      List.concat_nil, cs.wordProd_singleton] using cs.isReflection_simple j
  | succ n ih =>
    have hword : CoxeterSystem.alternatingWord i j (2 * (n + 1) + 1) =
        j :: (CoxeterSystem.alternatingWord j i (2 * n + 1) ++ [j]) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
        CoxeterSystem.alternatingWord_succ, List.concat_eq_append,
        CoxeterSystem.alternatingWord_succ']
      simp only [Nat.not_even_iff_odd.mpr (show Odd (2 * n + 1) from ⟨n, by omega⟩),
        ↓reduceIte, List.cons_append]
    rw [hword, cs.wordProd_cons, cs.wordProd_append, cs.wordProd_singleton]
    simpa only [cs.inv_simple, mul_assoc] using (ih j i).conj (cs.simple j)

/-- A rank-two Coxeter element is a reflection exactly when its Coxeter length is odd. -/
theorem rankTwo_reflection_iff (w : W) : cs.IsReflection w ↔ Odd (cs.length w) := by
  constructor
  · exact fun h => h.odd_length
  · intro hodd
    obtain ⟨word, hred, hword⟩ := cs.exists_isReduced w
    have hlen : Odd word.length := by rwa [hword, hred.eq] at hodd
    have hne : word ≠ [] := by
      intro heq
      rw [heq, List.length_nil] at hlen
      exact (by decide : ¬Odd (0 : ℕ)) hlen
    obtain ⟨i, heq⟩ := reduced_alternating cs hred hne
    have hprod := congrArg cs.wordProd heq
    obtain ⟨n, hn⟩ := hlen
    have hlength : word.length = 2 * n + 1 := by omega
    rw [hword, hprod, hlength]
    exact alternating_odd_reflection cs (!i) i n

/-- Rank-two Bruhat vertices are adjacent exactly when their lengths have opposite parity. -/
theorem rankTwo_adj_iff (x y : W) :
    (bruhatGraph cs).Adj x y ↔ Odd (cs.length x + cs.length y) := by
  change cs.IsReflection (y * x⁻¹) ↔ _
  rw [rankTwo_reflection_iff, Nat.odd_iff, Nat.odd_iff,
    cs.length_mul_mod_two, cs.length_inv, Nat.add_comm]

end BruhatIntervals
