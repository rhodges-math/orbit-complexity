import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyCoxeter
import Mathlib.GroupTheory.Coxeter.Length

/-!
# The constructed Coxeter length is the root-inversion count

Both lengths are compared through their simple words.
Inversion count bounds every expression and is attained by an expression;
the proved word and presentation comparisons therefore identify the
existing Coxeter length and reducedness APIs with the root counts.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The constructed Coxeter length on the Weyl group is exactly the
cardinality of its positive-to-negative root inversion set. -/
@[simp] theorem weylCoxeterSystem_length (b : P.Base) (w : P.weylGroup) :
    (weylCoxeterSystem b).length w = rootInversionCount b w := by
  apply le_antisymm
  · obtain ⟨l, hl, hlen⟩ := InversionLength.exists_of_inversionCount_length b w
    have hle := (weylCoxeterSystem b).length_wordProd_le l
    simpa only [weylCoxeterSystem_wordProd, hl, hlen] using hle
  · obtain ⟨l, hred, hprod⟩ := (weylCoxeterSystem b).exists_isReduced w
    calc
      rootInversionCount b w = rootInversionCount b (simpleWeylWord b l) := by
        rw [hprod, weylCoxeterSystem_wordProd]
      _ ≤ l.length := RootInversionCount.simpleWeylWord_le_length b l
      _ = (weylCoxeterSystem b).length w := by rw [hprod]; exact hred.symm

/-- The original formal Coxeter length also equals the inversion
count of its image under the canonical presentation isomorphism. -/
theorem FormalCoxeter.length_eq_rootInversionCount (b : P.Base)
    (x : (simpleCoxeterMatrix b).Group) :
    (simpleCoxeterMatrix b).toCoxeterSystem.length x =
      rootInversionCount b (weylCoxeterPresentationMap b x) := by
  obtain ⟨l, rfl⟩ := (simpleCoxeterMatrix b).toCoxeterSystem.wordProd_surjective x
  apply le_antisymm
  · obtain ⟨k, _, hklen, hkformal⟩ :=
    PresentationWordPropertyNormalization.exists_preserving_reduced_word b l
    have hle := (simpleCoxeterMatrix b).toCoxeterSystem.length_wordProd_le k
    rw [hkformal, hklen] at hle
    simpa only [weylCoxeterPresentationMap_wordProd] using hle
  · obtain ⟨k, hred, hprod⟩ := (simpleCoxeterMatrix b).toCoxeterSystem.exists_isReduced
      ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd l)
    have hle := RootInversionCount.simpleWeylWord_le_length b k
    rw [← weylCoxeterPresentationMap_wordProd, ← hprod] at hle
    have hklen : k.length = (simpleCoxeterMatrix b).toCoxeterSystem.length
        ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd l) := by
      rw [hprod]
      exact hred.symm
    simpa only [hklen] using hle

/-- Mathlib's reducedness predicate for `weylCoxeterSystem` is the
equality between word length and root inversion count. -/
theorem weylCoxeterSystem_isReduced_iff (b : P.Base) (l : List b.support) :
    (weylCoxeterSystem b).IsReduced l ↔
      rootInversionCount b (simpleWeylWord b l) = l.length := by
  simp only [CoxeterSystem.IsReduced, weylCoxeterSystem_wordProd,
    weylCoxeterSystem_length]

/-- Formal reducedness and reducedness agree for every word. -/
theorem formalCoxeter_isReduced_iff (b : P.Base) (l : List b.support) :
    (simpleCoxeterMatrix b).toCoxeterSystem.IsReduced l ↔
      rootInversionCount b (simpleWeylWord b l) = l.length := by
  simp only [CoxeterSystem.IsReduced, FormalCoxeter.length_eq_rootInversionCount,
    weylCoxeterPresentationMap_wordProd]

end ReductiveGroups
