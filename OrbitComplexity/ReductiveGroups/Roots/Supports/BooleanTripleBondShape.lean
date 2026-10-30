import OrbitComplexity.ReductiveGroups.Roots.Supports.TripleBondIsolation
import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanBondEquality

/-!
# Boolean Triple Bond Shape

The triple-bond case of the Boolean inversion shape:
a non-multiplicity-free inversion on an occupied triple bond is the long
simple root plus three copies of the short simple root.  -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- The equality is

```lean
(∀ k : b.support, simpleRootCoeffInt b β k =
      if k = p then 1 else if k = q then 3 else 0) ∧
      P.root β = P.root (p : ι) + (3 : ℤ) • P.root (q : ι)
```
-/
theorem leftRootInversion_triple_bond_shape
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    (β : ι) (hβ : P.root β ∈ leftRootInversions b (simpleWeylWord b word))
    (p q : b.support) (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1) :
    (∀ k : b.support, simpleRootCoeffInt b β k =
      if k = p then 1 else if k = q then 3 else 0) ∧
      P.root β = P.root (p : ι) + (3 : ℤ) • P.root (q : ι) := by
  have hpqne : p ≠ q := by
    intro h
    subst q
    rw [P.pairingIn_same] at hpq
    omega
  have hβpos : b.IsPos β :=
    ((mem_leftRootInversionIndices b _ β).mp
      ((root_mem_leftRootInversions b _ β).mp hβ)).1
  have hsupp := positiveRoot_triple_bond_support_eq_pair b β hβpos p q hp hq hpqne hpq hqp
  obtain ⟨L, i, T, hsplit, heq⟩ := leftRootInversion_exists_word_occurrence b word hword β hβ
  have hiL : i ∉ L := by
    rw [hsplit] at hword
    intro hi
    exact (List.nodup_append.mp hword).2.2 i hi i (by simp) rfl
  have hiOne : simpleRootCoeffInt b β i = 1 := by
    rw [heq]
    exact simpleWeylWord_initial_coeff_one b L i hiL
  have hiSupp : i ∈ simpleRootSupportInt b β := by
    change simpleRootCoeffInt b β i ≠ 0
    rw [hiOne]
    norm_num
  have hone : simpleRootCoeffInt b β p = 1 ∨ simpleRootCoeffInt b β q = 1 := by
    rw [hsupp] at hiSupp
    rcases hiSupp with h | h
    · exact Or.inl (h ▸ hiOne)
    · exact Or.inr (h ▸ hiOne)
  have hpWord := LeftRootInversion.support_letter_mem_word b word hword β hβ p hp
  have hqWord := LeftRootInversion.support_letter_mem_word b word hword β hβ q hq
  have hidx : word.idxOf p ≠ word.idxOf q :=
    fun h => hpqne ((List.idxOf_inj hpWord).mp h)
  have hrel : simpleRootCoeffInt b β p = simpleRootCoeffInt b β q ∨
      simpleRootCoeffInt b β q = 3 * simpleRootCoeffInt b β p := by
    rcases lt_or_gt_of_ne hidx with h | h
    · left
      have he := LeftRootInversion.bond_coefficient_eq_of_word_order b word hword β hβ
        p q hpqne (by rw [hqp]; norm_num) hp hq h
      simpa [hqp] using he
    · right
      have he := LeftRootInversion.bond_coefficient_eq_of_word_order b word hword β hβ
        q p hpqne.symm (by rw [hpq]; norm_num) hq hp h
      simpa [hpq, mul_comm] using he
  have hneq : simpleRootCoeffInt b β p ≠ simpleRootCoeffInt b β q := by
    intro he
    have hcp : simpleRootCoeffInt b β p = 1 := by omega
    have hcq : simpleRootCoeffInt b β q = 1 := by omega
    apply hbad
    intro k
    by_cases hk : k ∈ simpleRootSupportInt b β
    · rw [hsupp] at hk
      rcases hk with h | h
      · exact Or.inr (h ▸ hcp)
      · exact Or.inr (h ▸ hcq)
    · exact Or.inl (by simpa only [simpleRootSupportInt, Set.mem_ofPred_eq, not_not] using hk)
  have hthree := hrel.resolve_left hneq
  have hcp : simpleRootCoeffInt b β p = 1 := by omega
  have hcq : simpleRootCoeffInt b β q = 3 := by omega
  have hcoeff (k : b.support) : simpleRootCoeffInt b β k =
      if k = p then 1 else if k = q then 3 else 0 := by
    by_cases hkp : k = p
    · subst k
      simp [hcp]
    · by_cases hkq : k = q
      · subst k
        simp [hcq, hpqne.symm]
      · have hz : simpleRootCoeffInt b β k = 0 := by
          by_contra hn
          have hm : k ∈ simpleRootSupportInt b β := hn
          rw [hsupp] at hm
          exact hm.elim hkp hkq
        simp [hkp, hkq, hz]
  refine ⟨hcoeff, ?_⟩
  have hspan : P.rootSpanMem ℤ β = P.rootSpanMem ℤ (p : ι) +
      (3 : ℤ) • P.rootSpanMem ℤ (q : ι) := by
    apply b.toWeightBasisInt.repr.injective
    apply Finsupp.ext
    intro k
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    change simpleRootCoeffInt b β k =
      simpleRootCoeffInt b (p : ι) k + 3 * simpleRootCoeffInt b (q : ι) k
    rw [hcoeff, simpleRootCoeffInt_simple, simpleRootCoeffInt_simple]
    by_cases hkp : k = p
    · subst k
      simp [hpqne.symm]
    · by_cases hkq : k = q
      · subst k
        simp [hpqne, hpqne.symm]
      · simp [hkp, hkq, Ne.symm hkp, Ne.symm hkq]
  exact congrArg Subtype.val hspan

end ReductiveGroups
