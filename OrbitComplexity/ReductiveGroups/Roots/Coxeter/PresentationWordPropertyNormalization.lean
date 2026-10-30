import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordProperty

/-!
# Presentation-preserving normalization of arbitrary simple words

Normalize a prefix first. An ascent appends a letter to the reduced word.
For a descent, choose a reduced expression for the shorter element;
appending the final letter to it is a reduced expression for the previous
prefix. The proved reduced-word equality identifies those two expressions
in the formal presentation, where the final repeated simple cancels.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Every word has a reduced representative with the same
product both in the Weyl group and in the formal presentation. -/
theorem PresentationWordPropertyNormalization.exists_preserving_reduced_word (b : P.Base)
    (l : List b.support) :
    ∃ k : List b.support,
      simpleWeylWord b k = simpleWeylWord b l ∧
      k.length = rootInversionCount b (simpleWeylWord b l) ∧
      (simpleCoxeterMatrix b).toCoxeterSystem.wordProd k =
        (simpleCoxeterMatrix b).toCoxeterSystem.wordProd l := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp [simpleWeylWord], rfl⟩
  | append_singleton l i ih =>
    obtain ⟨k, hk, hklen, hkformal⟩ := ih
    have happ : simpleWeylWord b (l ++ [i]) =
        simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i := by
      simp only [simpleWeylWord_append, simpleWeylWord, mul_one]
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)
    · refine ⟨k ++ [i], ?_, ?_, ?_⟩
      · simp only [simpleWeylWord_append, hk]
      · rw [List.length_append, List.length_singleton, hklen, happ,
          rootInversionCount_mul_simple_of_pos b _ i hpos]
      · simp only [CoxeterSystem.wordProd_append, hkformal]
    · have hneg := (root_height_neg_iff_not_isPos b _).mpr hpos
      have hdrop := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) i hneg
      obtain ⟨r, hr, hrlen⟩ := InversionLength.exists_of_inversionCount_length b
        (simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i)
      have hreturn : simpleWeylWord b (r ++ [i]) = simpleWeylWord b l := by
        simp only [simpleWeylWord_append, simpleWeylWord, mul_one, hr,
          mul_assoc, weylGroup_ofIdx_mul_self]
      have hkred : rootInversionCount b (simpleWeylWord b k) = k.length := by
        rw [hk, hklen]
      have hrred : rootInversionCount b (simpleWeylWord b (r ++ [i])) =
          (r ++ [i]).length := by
        rw [hreturn, List.length_append, List.length_singleton, hrlen]
        exact hdrop.symm
      have heq := presentationWordProd_eq_of_reduced b k (r ++ [i]) hkred hrred
        (hk.trans hreturn.symm)
      refine ⟨r, hr.trans happ.symm, by rw [happ]; exact hrlen, ?_⟩
      calc
        (simpleCoxeterMatrix b).toCoxeterSystem.wordProd r =
            (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (r ++ [i]) *
              (simpleCoxeterMatrix b).toCoxeterSystem.simple i := by
          rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
            CoxeterSystem.simple_mul_simple_cancel_right]
        _ = (simpleCoxeterMatrix b).toCoxeterSystem.wordProd k *
              (simpleCoxeterMatrix b).toCoxeterSystem.simple i := by rw [← heq]
        _ = (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (l ++ [i]) := by
          rw [hkformal, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton]

end ReductiveGroups
