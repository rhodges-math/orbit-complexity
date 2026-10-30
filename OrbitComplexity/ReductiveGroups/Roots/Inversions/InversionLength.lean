import OrbitComplexity.ReductiveGroups.Roots.Coxeter.Exchange

/-!
# Inversion count is minimum simple-word length

Exchange constructs an expression attaining the inversion-count lower bound.
For a positive final simple-root image we append the last letter; for a
negative image we delete a letter using the exchange theorem.
Thus the inversion count is the minimum over all simple expressions,
without a Coxeter-system assumption or a definition imposing this equality.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Every expression can be replaced by one attaining the
inversion-count lower bound. -/
theorem SimpleWeylWord.has_expression_of_inversionCount_length
    (b : P.Base) (l : List b.support) :
    ∃ m : List b.support, simpleWeylWord b m = simpleWeylWord b l ∧
      m.length = rootInversionCount b (simpleWeylWord b l) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp [simpleWeylWord]⟩
  | append_singleton l i ih =>
    obtain ⟨m, hm, hlength⟩ := ih
    have happ : simpleWeylWord b (l ++ [i]) =
        simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i := by
      simp [simpleWeylWord_append, simpleWeylWord]
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)
    · refine ⟨m ++ [i], ?_, ?_⟩
      · simp only [simpleWeylWord_append, simpleWeylWord, mul_one, hm]
      · rw [List.length_append, List.length_singleton, hlength, happ,
          rootInversionCount_mul_simple_of_pos b (simpleWeylWord b l) i hpos]
    · have hneg : b.height (P.weylGroupToPerm (simpleWeylWord b m) i) < 0 := by
        rw [hm]
        exact (root_height_neg_iff_not_isPos b _).mpr hpos
      obtain ⟨m', hprod, hlength'⟩ := Exchange.exists_simpleWeylWord_of_negative b m i hneg
      refine ⟨m', ?_, ?_⟩
      · rw [hprod, hm, happ]
      · have hcount := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) i
          ((root_height_neg_iff_not_isPos b _).mpr hpos)
        rw [happ]
        omega

/-- Every Weyl element has an expression with length exactly its
root-inversion count. -/
theorem InversionLength.exists_of_inversionCount_length (b : P.Base) (w : P.weylGroup) :
    ∃ l : List b.support, simpleWeylWord b l = w ∧ l.length = rootInversionCount b w := by
  obtain ⟨l, rfl⟩ := simpleWeylWord_surjective b w
  exact SimpleWeylWord.has_expression_of_inversionCount_length b l

/-- The inversion count is the least length of all simple
expressions for the Weyl element. -/
theorem rootInversionCount_isLeast_wordLength (b : P.Base) (w : P.weylGroup) :
    IsLeast {n : ℕ | ∃ l : List b.support, simpleWeylWord b l = w ∧ l.length = n}
      (rootInversionCount b w) := by
  refine ⟨InversionLength.exists_of_inversionCount_length b w, ?_⟩
  rintro n ⟨l, hl, hlength⟩
  simpa only [hl, hlength] using RootInversionCount.simpleWeylWord_le_length b l

/-- A Weyl element with no root inversions is the identity. -/
@[simp] theorem rootInversionCount_eq_zero_iff (b : P.Base) (w : P.weylGroup) :
    rootInversionCount b w = 0 ↔ w = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, hlength⟩ := InversionLength.exists_of_inversionCount_length b w
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (hlength.trans h)
    simpa only [hnil, simpleWeylWord] using hl.symm
  · rintro rfl
    exact rootInversionCount_one b

end ReductiveGroups
