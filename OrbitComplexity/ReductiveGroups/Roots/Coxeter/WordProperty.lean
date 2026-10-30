import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordPropertyBraid

/-!
# The Word Property for reduced Weyl words

Strong induction on reduced length constructs a finite sequence of
braid replacements. The equal-final-letter case lifts a shorter chain to
a common suffix; the distinct-final-letter case uses the constructed
common-descent braid diamond. Equality in the formal presentation is not
used to infer the existence of a chain.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Two reduced simple words with the same product are connected by
a finite chain of contextual braid replacements. -/
theorem weylBraidChain_of_reduced (b : P.Base)
    (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k) : WeylBraidChain b l k := by
  have aux : ∀ n : ℕ, ∀ l k : List b.support, l.length = n →
      rootInversionCount b (simpleWeylWord b l) = l.length →
      rootInversionCount b (simpleWeylWord b k) = k.length →
      simpleWeylWord b l = simpleWeylWord b k → WeylBraidChain b l k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l k hlen hl hk heq
      have same_last (p q : List b.support) (s : b.support)
          (hp_lt : p.length < n)
          (hp : rootInversionCount b (simpleWeylWord b p) = p.length)
          (hq : rootInversionCount b (simpleWeylWord b q) = q.length)
          (hprod : simpleWeylWord b (p ++ [s]) = simpleWeylWord b (q ++ [s])) :
          WeylBraidChain b (p ++ [s]) (q ++ [s]) := by
        have hpq : simpleWeylWord b p = simpleWeylWord b q :=
          mul_right_cancel (by simpa only [simpleWeylWord_append, simpleWeylWord,
            mul_one] using hprod)
        exact (ih p.length hp_lt p q rfl hp hq hpq).append_right [s]
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
        exists_reduced_braid_move_diamond b (simpleWeylWord b (l ++ [i])) i j hij hi hj
      have hupre := RootInversionCount.prefix_of_reduced_append_singleton b u i hured
      have hvpre := RootInversionCount.prefix_of_reduced_append_singleton b v j hvred
      exact (same_last l u i hllt hlpre hupre hu.symm).trans
        ((Relation.ReflTransGen.single hbraid).trans
          (WeylBraidChain.symm (same_last k v j hklt hkpre hvpre (heq.symm.trans hv.symm))))
  exact aux l.length l k rfl hl hk heq

/-- The Word Property with an explicit finite list of consecutive words. -/
theorem exists_reduced_braid_path (b : P.Base) (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k) :
    ∃ path : List (List b.support),
      List.IsChain (WeylBraidMove b) (l :: path) ∧
      (l :: path).getLast (List.cons_ne_nil _ _) = k :=
  (weylBraidChain_of_reduced b l k hl hk heq).exists_list

/-- The explicit path consists entirely of reduced expressions for the
same Weyl element. -/
theorem exists_reduced_braid_path_all_reduced (b : P.Base) (l k : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length)
    (hk : rootInversionCount b (simpleWeylWord b k) = k.length)
    (heq : simpleWeylWord b l = simpleWeylWord b k) :
    ∃ path : List (List b.support),
      List.IsChain (WeylBraidMove b) (l :: path) ∧
      (l :: path).getLast (List.cons_ne_nil _ _) = k ∧
      ∀ r ∈ l :: path,
        rootInversionCount b (simpleWeylWord b r) = r.length ∧
        simpleWeylWord b r = simpleWeylWord b l := by
  obtain ⟨path, hchain, hlast⟩ := exists_reduced_braid_path b l k hl hk heq
  refine ⟨path, hchain, hlast, ?_⟩
  refine hchain.induction (fun r =>
    rootInversionCount b (simpleWeylWord b r) = r.length ∧
      simpleWeylWord b r = simpleWeylWord b l) (l :: path) ?_ ?_
  · intro x y hmove hx
    refine ⟨?_, hmove.simpleWeylWord_eq.symm.trans hx.2⟩
    simpa only [← hmove.simpleWeylWord_eq, ← hmove.length_eq] using hx.1
  · intro _
    exact ⟨hl, rfl⟩

/-- The same chain through the constructed Coxeter API. -/
theorem weylCoxeterSystem_word_property (b : P.Base) (l k : List b.support)
    (hl : (weylCoxeterSystem b).IsReduced l)
    (hk : (weylCoxeterSystem b).IsReduced k)
    (heq : (weylCoxeterSystem b).wordProd l =
      (weylCoxeterSystem b).wordProd k) : WeylBraidChain b l k := by
  apply weylBraidChain_of_reduced b l k
  · exact (weylCoxeterSystem_isReduced_iff b l).mp hl
  · exact (weylCoxeterSystem_isReduced_iff b k).mp hk
  · simpa only [weylCoxeterSystem_wordProd] using heq

end ReductiveGroups
