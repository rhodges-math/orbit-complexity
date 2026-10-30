import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BraidMoves

/-! # The common-descent diamond with a braid move -/

noncomputable section

namespace ReductiveGroups

open CoxeterSystem

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The common-descents construction retains the common prefix and
opposite full braid words, so the final comparison is one braid move. -/
theorem exists_reduced_braid_move_diamond (b : P.Base)
    (w : P.weylGroup) (i j : b.support) (hij : i ≠ j)
    (hi : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) < rootInversionCount b w)
    (hj : rootInversionCount b (w * RootPairing.weylGroup.ofIdx P j) < rootInversionCount b w) :
    ∃ l k : List b.support,
      simpleWeylWord b (l ++ [i]) = w ∧
      rootInversionCount b (simpleWeylWord b (l ++ [i])) = (l ++ [i]).length ∧
      simpleWeylWord b (k ++ [j]) = w ∧
      rootInversionCount b (simpleWeylWord b (k ++ [j])) = (k ++ [j]).length ∧
      WeylBraidMove b (l ++ [i]) (k ++ [j]) := by
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
  · exact ⟨r, [], j, i, hij.symm,
      by simp only [List.append_nil, List.append_assoc, ← hBi]; rfl,
      by simp only [List.append_nil, List.append_assoc, ← hBj]; rfl⟩

end ReductiveGroups
