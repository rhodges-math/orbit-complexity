import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralDescents

/-!
# Reduced common-descent words joined by a formal braid relation

The common-descent reduction supplies a shorter Weyl element. A
minimum-length expression for it, followed by either rank-two braid word,
gives two reduced expressions for the original element. Their
products agree in the formal presentation by its defining braid identity.

-/

noncomputable section

namespace ReductiveGroups

open CoxeterSystem

/-- Reversing an alternating word either preserves it or exchanges its two
letters, according to its length parity. -/
theorem reverse_alternatingWord {B : Type*} (i j : B) (n : ℕ) :
    (alternatingWord i j n).reverse =
      if Even n then alternatingWord j i n else alternatingWord i j n := by
  induction n generalizing i j with
  | zero => simp [alternatingWord]
  | succ n ih =>
    conv_lhs => rw [alternatingWord_succ, List.concat_eq_append, List.reverse_concat, ih]
    by_cases hn : Even n
    · simp only [hn, ite_true, Nat.even_add_one, not_true_eq_false, ite_false]
      rw [alternatingWord_succ']
      simp only [hn, ite_true]
    · simp only [hn, ite_false, Nat.even_add_one, not_false_eq_true, ite_true]
      rw [alternatingWord_succ']
      simp only [hn, ite_false]

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The full braid product is an involution already in the formal
presentation. This is a consequence of reversal and the braid relation. -/
theorem presentationWordProd_braidWord_inv (b : P.Base) (i j : b.support) :
    ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd
      (braidWord (simpleCoxeterMatrix b) i j))⁻¹ =
    (simpleCoxeterMatrix b).toCoxeterSystem.wordProd
      (braidWord (simpleCoxeterMatrix b) i j) := by
  rw [← wordProd_reverse, reverse_alternatingWord]
  split_ifs
  · simpa only [braidWord, (simpleCoxeterMatrix b).symmetric j i] using
      ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd_braidWord_eq i j).symm
  · rfl

/-- The same involution identity for the braid word, transported
only in the forward direction along the presentation homomorphism. -/
theorem simpleWeylWord_braidWord_mul_self (b : P.Base) (i j : b.support) :
    simpleWeylWord b (braidWord (simpleCoxeterMatrix b) i j) *
      simpleWeylWord b (braidWord (simpleCoxeterMatrix b) i j) = 1 := by
  have h := mul_inv_cancel
    ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd
      (braidWord (simpleCoxeterMatrix b) i j))
  rw [presentationWordProd_braidWord_inv] at h
  simpa only [map_mul, map_one, weylCoxeterPresentationMap_wordProd] using
    congrArg (weylCoxeterPresentationMap b) h

/-- Removing the final letter of a reduced word preserves
reducedness, by the inversion-count upper bound for one appended letter. -/
theorem RootInversionCount.prefix_of_reduced_append_singleton (b : P.Base)
    (l : List b.support) (i : b.support)
    (hred : rootInversionCount b (simpleWeylWord b (l ++ [i])) = (l ++ [i]).length) :
    rootInversionCount b (simpleWeylWord b l) = l.length := by
  have hbound := RootInversionCount.simpleWeylWord_le_length b l
  have hstep := rootInversionCount_mul_simple_le b (simpleWeylWord b l) i
  simp only [simpleWeylWord_append, simpleWeylWord, mul_one,
    List.length_append, List.length_singleton] at hred
  omega

/-- Two distinct right descents give reduced expressions ending in the
respective letters whose formal products agree by one braid relation after
a common prefix.  -/
theorem PresentationWordPropertyBraid.exists_presentation_braid_diamond (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) < rootInversionCount b w)
    (hj : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P j) < rootInversionCount b w) :
    ∃ l k : List b.support,
      simpleWeylWord b (l ++ [i]) = w ∧
      rootInversionCount b (simpleWeylWord b (l ++ [i])) = (l ++ [i]).length ∧
      simpleWeylWord b (k ++ [j]) = w ∧
      rootInversionCount b (simpleWeylWord b (k ++ [j])) = (k ++ [j]).length ∧
      (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (l ++ [i]) =
        (simpleCoxeterMatrix b).toCoxeterSystem.wordProd (k ++ [j]) := by
  let C := simpleCoxeterMatrix b
  let z := simpleWeylWord b (braidWord C i j)
  have hdrop := RootInversionCount.mul_braidWord_of_common_descents b w i j hij hi hj
  obtain ⟨r, hr, hrlen⟩ := InversionLength.exists_of_inversionCount_length b (w * z)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (simpleCoxeterMatrix_pos b i j))
  have hBi : braidWord C j i = alternatingWord i j t ++ [i] := by
    change alternatingWord j i (C j i) = _
    rw [C.symmetric j i, ht, alternatingWord_succ, List.concat_eq_append]
  have hBj : braidWord C i j = alternatingWord j i t ++ [j] := by
    change alternatingWord i j (C i j) = _
    rw [ht, alternatingWord_succ, List.concat_eq_append]
  have hprodj : simpleWeylWord b (r ++ braidWord C i j) = w := by
    rw [simpleWeylWord_append, hr]
    change w * z * z = w
    rw [mul_assoc, simpleWeylWord_braidWord_mul_self, mul_one]
  have hprodi : simpleWeylWord b (r ++ braidWord C j i) = w := by
    rw [simpleWeylWord_append]
    change simpleWeylWord b r *
      simpleWeylWord b (braidWord (simpleCoxeterMatrix b) j i) = w
    rw [simpleWeylWord_braidWord_eq b j i]
    simpa only [simpleWeylWord_append] using hprodj
  have hlenj : (r ++ braidWord C i j).length = rootInversionCount b w := by
    simp only [List.length_append, length_alternatingWord, hrlen]
    exact hdrop
  have hleni : (r ++ braidWord C j i).length = rootInversionCount b w := by
    simpa only [List.length_append, length_alternatingWord, C.symmetric j i] using hlenj
  refine ⟨r ++ alternatingWord i j t, r ++ alternatingWord j i t, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, ← hBi] using hprodi
  · simpa only [List.append_assoc, ← hBi, hprodi] using hleni.symm
  · simpa only [List.append_assoc, ← hBj] using hprodj
  · simpa only [List.append_assoc, ← hBj, hprodj] using hlenj.symm
  · simp only [List.append_assoc, ← hBi, ← hBj, wordProd_append]
    rw [C.toCoxeterSystem.wordProd_braidWord_eq j i]

end ReductiveGroups
