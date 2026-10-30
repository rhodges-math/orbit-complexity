import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyBraid

/-!
# Formal equality of reduced simple words

Induction on reduced-word length compares the final letters. Equal
letters cancel. Distinct final letters are common right descents; the
checked rank-two reduction produces two reduced words sharing a prefix and
joined by the formal braid identity. The induction hypothesis applies only
after their final letters have been removed.

The conclusion is an equality in the canonical Coxeter presentation. No
Coxeter system on the Weyl group, presentation injectivity, or word
property is assumed. The ambient module need not be spanned by roots.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Any two reduced expressions of the same Weyl element have equal
products in the formal Coxeter presentation, by length induction and the
proved common-right-descent braid reduction. -/
theorem presentationWordProd_eq_of_reduced (b : P.Base)
    (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k) :
    (simpleCoxeterMatrix b).toCoxeterSystem.wordProd l =
      (simpleCoxeterMatrix b).toCoxeterSystem.wordProd k := by
  have aux : ∀ n : ℕ, ∀ l k : List b.support, l.length = n →
      rootInversionCount b (simpleWeylWord b l) = l.length →
      rootInversionCount b (simpleWeylWord b k) = k.length →
      simpleWeylWord b l = simpleWeylWord b k →
      (simpleCoxeterMatrix b).toCoxeterSystem.wordProd l =
        (simpleCoxeterMatrix b).toCoxeterSystem.wordProd k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l k hlen hl hk heq
      have same_last (p q : List b.support) (s : b.support)
          (hp_lt : p.length < n)
          (hp : rootInversionCount b (simpleWeylWord b p) = p.length)
          (hq : rootInversionCount b (simpleWeylWord b q) = q.length)
          (hprod : simpleWeylWord b (p ++ [s]) = simpleWeylWord b (q ++ [s])) :
          (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (p ++ [s]) =
            (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (q ++ [s]) := by
        have hpq : simpleWeylWord b p = simpleWeylWord b q :=
          mul_right_cancel (by simpa only [simpleWeylWord_append, simpleWeylWord,
            mul_one] using hprod)
        have hformal := ih p.length hp_lt p q rfl hp hq hpq
        simp only [CoxeterSystem.wordProd_append, hformal]
      have hlen_eq : l.length = k.length := by rw [← hl, ← hk, heq]
      rcases List.eq_nil_or_concat' l with rfl | ⟨l, i, rfl⟩
      · have hknil : k = [] := List.eq_nil_of_length_eq_zero hlen_eq.symm
        rw [hknil]
      rcases List.eq_nil_or_concat' k with rfl | ⟨k, j, rfl⟩
      · simp only [List.length_append, List.length_singleton, List.length_nil] at hlen_eq
        omega
      have hlpre := RootInversionCount.prefix_of_reduced_append_singleton b l i hl
      have hkpre := RootInversionCount.prefix_of_reduced_append_singleton b k j hk
      have hllt : l.length < n := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hklt : k.length < n := by
        simp only [List.length_append, List.length_singleton] at hlen_eq hlen
        omega
      by_cases hij : i = j
      · subst j
        exact same_last l k i hllt hlpre hkpre heq
      have hcancel (p : List b.support) (s : b.support) :
          simpleWeylWord b (p ++ [s]) * RootPairing.weylGroup.ofIdx P s =
            simpleWeylWord b p := by
        simp only [simpleWeylWord_append, simpleWeylWord, mul_one,
          mul_assoc, weylGroup_ofIdx_mul_self]
      have hi : rootInversionCount b
          (simpleWeylWord b (l ++ [i]) * RootPairing.weylGroup.ofIdx P i) <
            rootInversionCount b (simpleWeylWord b (l ++ [i])) := by
        rw [hcancel, hlpre, hl]
        simp
      have hj : rootInversionCount b
          (simpleWeylWord b (l ++ [i]) * RootPairing.weylGroup.ofIdx P j) <
            rootInversionCount b (simpleWeylWord b (l ++ [i])) := by
        rw [heq, hcancel, hkpre, hk]
        simp
      obtain ⟨u, v, hu, hured, hv, hvred, hbraid⟩ :=
        PresentationWordPropertyBraid.exists_presentation_braid_diamond b (simpleWeylWord b (l ++
          [i])) i j hij hi hj
      have hupre := RootInversionCount.prefix_of_reduced_append_singleton b u i hured
      have hvpre := RootInversionCount.prefix_of_reduced_append_singleton b v j hvred
      calc
        (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (l ++ [i]) =
            (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (u ++ [i]) :=
          same_last l u i hllt hlpre hupre hu.symm
        _ = (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (v ++ [j]) := hbraid
        _ = (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (k ++ [j]) :=
          (same_last k v j hklt hkpre hvpre (heq.symm.trans hv.symm)).symm
  exact aux l.length l k rfl hl hk heq

end ReductiveGroups
