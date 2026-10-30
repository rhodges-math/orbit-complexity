import OrbitComplexity.BruhatIntervals.Words.Subexpression

/-! # Subexpressions determined by prefix products

Each simple reflection is nonidentity, so equality of consecutive prefix products
recovers whether the corresponding letter was retained. The entire prefix path
therefore determines the subexpression, without a reducedness assumption.
-/

namespace BruhatIntervals
universe u v
variable {S : Type u} {W : Type v} [Group W] {M : CoxeterMatrix S}
  (cs : CoxeterSystem M W)

/-- A subexpression is determined by all its prefix products. -/
theorem Subexpression.eq_of_prefixProd {word : List S} (a b : Subexpression word)
    (h : ∀ k ≤ word.length, a.prefixProd cs k = b.prefixProd cs k) : a = b := by
  have hc : a.choices = b.choices := by
    apply List.ext_getElem
    · exact a.length_choices.trans b.length_choices.symm
    · intro j hja hjb
      have hjword : j < word.length := by rw [← a.length_choices]; exact hja
      let p : Fin word.length := ⟨j, hjword⟩
      have hzero := h j (Nat.le_of_lt p.isLt)
      have hnext := h (j + 1) p.isLt
      rw [a.prefixProd_succ cs p, b.prefixProd_succ cs p] at hnext
      change a.prefixProd cs j * _ = b.prefixProd cs j * _ at hnext
      rw [hzero] at hnext
      have hi := mul_left_cancel hnext
      change (if a.choices[j] then cs.simple word[j] else 1) =
        (if b.choices[j] then cs.simple word[j] else 1) at hi
      have hne : cs.simple word[j] ≠ 1 := by
        intro hs
        have hl := cs.length_simple word[j]
        rw [hs, cs.length_one] at hl
        omega
      cases ha : a.choices[j] <;> cases hb : b.choices[j]
      · rfl
      · exfalso
        apply hne
        exact (show (1 : W) = cs.simple word[j] by simpa [ha, hb] using hi).symm
      · exfalso
        apply hne
        simpa [ha, hb] using hi
      · rfl
  cases a
  cases b
  cases hc
  rfl

end BruhatIntervals
