import OrbitComplexity.ReductiveGroups.Roots.Supports.TripleBondPositiveRoots

/-!
# Boolean Triple Bond Inversions

The two Boolean inversions that can live on an occupied triple bond. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem root_eq_of_simpleRootCoeffInt_eq (b : P.Base) (x y : ι)
    (h : ∀ k : b.support,
      simpleRootCoeffInt b x k = simpleRootCoeffInt b y k) : x = y := by
  apply P.root.injective
  have heq : P.rootSpanMem ℤ x = P.rootSpanMem ℤ y := by
    apply b.toWeightBasisInt.repr.injective
    apply Finsupp.ext
    intro k
    exact h k
  exact congrArg Subtype.val heq

/-- In a distinct-letter word with a non-`0/1` inversion occupying a
triple bond, every inversion supported on the two bond vertices
is either its short simple root or that same non-`0/1` inversion. -/
theorem LeftRootInversion.triple_bond_supported_eq_short_or_large
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    (β : ι) (hβ : P.root β ∈ leftRootInversions b (simpleWeylWord b word))
    (p q : b.support)
    (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1)
    (δ : ι) (hδ : P.root δ ∈ leftRootInversions b (simpleWeylWord b word))
    (hδsupp : simpleRootSupportInt b δ ⊆ ({p, q} : Set b.support)) :
    δ = (q : ι) ∨ δ = β := by
  have hpqne : p ≠ q := by
    intro h
    subst q
    rw [P.pairingIn_same] at hpq
    omega
  have hβshape :=
    leftRootInversion_triple_bond_shape b word hword β hβ p q hp hq hpq hqp hbad
  have hβp : simpleRootCoeffInt b β p = 1 := by
    simpa [hpqne] using hβshape.1 p
  have hβq : simpleRootCoeffInt b β q = 3 := by
    simpa [hpqne.symm] using hβshape.1 q
  have hpWord : p ∈ word := LeftRootInversion.support_letter_mem_word
    b word hword β hβ p (by rw [hβp]; norm_num)
  have hqWord : q ∈ word := LeftRootInversion.support_letter_mem_word
    b word hword β hβ q (by rw [hβq]; norm_num)
  have hidxne : word.idxOf p ≠ word.idxOf q := by
    intro he
    exact hpqne ((List.idxOf_inj hpWord).mp he)
  have hqBefore : word.idxOf q < word.idxOf p := by
    rcases lt_or_gt_of_ne hidxne with h | h
    · have hbound := LeftRootInversion.bond_coefficient_lower_of_word_order
        b word hword β hβ p q hpqne (by rw [hβq]; norm_num) h
      rw [hβp, hβq, hqp] at hbound
      omega
    · exact h
  have hδpos : b.IsPos δ :=
    ((mem_leftRootInversionIndices b _ δ).mp
      ((root_mem_leftRootInversions b _ δ).mp hδ)).1
  have hcoords := positiveRoot_tripleBond_coordinates b p q hpq hqp δ hδpos hδsupp
  have hδbound : 3 * simpleRootCoeffInt b δ p ≤
      simpleRootCoeffInt b δ q := by
    by_cases hdp : simpleRootCoeffInt b δ p = 0
    · have hqnonneg := simpleRootCoeffInt_nonneg_of_isPos b δ hδpos q
      omega
    · have hbound := LeftRootInversion.bond_coefficient_lower_of_word_order
        b word hword δ hδ q p hpqne.symm hdp hqBefore
      rw [hpq] at hbound
      omega
  have hδcases :
      (simpleRootCoeffInt b δ p = 0 ∧ simpleRootCoeffInt b δ q = 1) ∨
      (simpleRootCoeffInt b δ p = 1 ∧ simpleRootCoeffInt b δ q = 3) := by
    rcases hcoords with h | h | h | h | h | h <;> omega
  rcases hδcases with hshort | hlarge
  · left
    apply root_eq_of_simpleRootCoeffInt_eq b
    intro k
    by_cases hkp : k = p
    · subst k
      rw [hshort.1, simpleRootCoeffInt_simple, ite_eq_right hpqne.symm]
    · by_cases hkq : k = q
      · subst k
        rw [hshort.2, simpleRootCoeffInt_simple, ite_eq_left rfl]
      · have hz : simpleRootCoeffInt b δ k = 0 := by
          by_contra hn
          exact (hδsupp hn).elim hkp hkq
        simp [hz, simpleRootCoeffInt_simple, Ne.symm hkq]
  · right
    apply root_eq_of_simpleRootCoeffInt_eq b
    intro k
    by_cases hkp : k = p
    · subst k
      exact hlarge.1.trans hβp.symm
    · by_cases hkq : k = q
      · subst k
        exact hlarge.2.trans hβq.symm
      · have hz : simpleRootCoeffInt b δ k = 0 := by
          by_contra hn
          exact (hδsupp hn).elim hkp hkq
        rw [hz, hβshape.1 k]
        simp [hkp, hkq]

end ReductiveGroups
