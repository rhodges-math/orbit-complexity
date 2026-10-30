import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanTripleBondShortInversion
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSummandBounds
import OrbitComplexity.ReductiveGroups.Roots.Inversions.RootExpressionAuxiliaryOccurrence

/-!
# Triple Bond Expression

Admissible positive-root expressions of a non-`0/1`
Boolean triple-bond inversion. Occurrences remain a multiset. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem root_eq_of_pair_coefficients (b : P.Base) (p q : b.support)
    (x y : ι)
    (hx : simpleRootSupportInt b x ⊆ ({p, q} : Set b.support))
    (hy : simpleRootSupportInt b y ⊆ ({p, q} : Set b.support))
    (hp : simpleRootCoeffInt b x p = simpleRootCoeffInt b y p)
    (hq : simpleRootCoeffInt b x q = simpleRootCoeffInt b y q) : x = y := by
  apply P.root.injective
  have heq : P.rootSpanMem ℤ x = P.rootSpanMem ℤ y := by
    apply b.toWeightBasisInt.repr.injective
    apply Finsupp.ext
    intro k
    change simpleRootCoeffInt b x k = simpleRootCoeffInt b y k
    by_cases hkp : k = p
    · subst k; exact hp
    by_cases hkq : k = q
    · subst k; exact hq
    have hx0 : simpleRootCoeffInt b x k = 0 := by
      by_contra hn; exact (hx hn).elim hkp hkq
    have hy0 : simpleRootCoeffInt b y k = 0 := by
      by_contra hn; exact (hy hn).elim hkp hkq
    rw [hx0, hy0]
  exact congrArg Subtype.val heq

private theorem positive_tripleBond_zero_long_eq_short (b : P.Base)
    (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (γ : ι) (hγ : b.IsPos γ)
    (hsupp : simpleRootSupportInt b γ ⊆ ({p, q} : Set b.support))
    (hpzero : simpleRootCoeffInt b γ p = 0) : γ = (q : ι) := by
  have hpqne : p ≠ q := by
    intro h; subst q; rw [P.pairingIn_same] at hpq; omega
  have hcoords := positiveRoot_tripleBond_coordinates b p q hpq hqp γ hγ hsupp
  have hqone : simpleRootCoeffInt b γ q = 1 := by
    rcases hcoords with h | h | h | h | h | h <;> omega
  apply root_eq_of_pair_coefficients b p q γ (q : ι) hsupp
  · intro k hk
    rw [simpleRootSupportInt_simple_eq] at hk
    exact Or.inr hk
  · simpa [simpleRootCoeffInt_simple, hpqne.symm] using hpzero
  · simpa [simpleRootCoeffInt_simple] using hqone

/-- Every admissible expression has exactly one auxiliary occurrence;
all remaining occurrences are the short-simple inversion. No
minimality or irreducibility assumption is used. -/
theorem tripleBond_rootExpression_shape
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    (β : ι) (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (p q : b.support)
    (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1)
    (A D : Set ι)
    (hA : Disjoint A (leftRootInversionIndices b (simpleWeylWord b word)))
    (hApos : ∀ γ ∈ A, b.IsPos γ)
    (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b word))
    (hβD : β ∉ D)
    (s : Multiset ι) (hs : RootExpression P A D β s) :
    ∃ (τ : ι) (m : ℕ), τ ∈ A ∧ (q : ι) ∈ D ∧
      1 ≤ m ∧ m ≤ 3 ∧
      s = {τ} + Multiset.replicate m (q : ι) ∧
      simpleRootCoeffInt b τ p = 1 ∧
      simpleRootCoeffInt b τ q = 3 - m := by
  classical
  have hβroot : P.root β ∈ leftRootInversions b (simpleWeylWord b word) :=
    ⟨β, hβ, rfl⟩
  have hshape :=
    leftRootInversion_triple_bond_shape b word hword β hβroot p q hp hq hpq hqp hbad
  have hpqne : p ≠ q := by
    intro h; subst q; rw [P.pairingIn_same] at hpq; omega
  have hβp : simpleRootCoeffInt b β p = 1 := by
    simpa [hpqne] using hshape.1 p
  have hβq : simpleRootCoeffInt b β q = 3 := by
    simpa [hpqne.symm] using hshape.1 q
  have hβsupp : simpleRootSupportInt b β ⊆ ({p, q} : Set b.support) := by
    intro k hk
    by_contra hn
    have hkp : k ≠ p := fun he => hn (Or.inl he)
    have hkq : k ≠ q := fun he => hn (Or.inr he)
    have hz : simpleRootCoeffInt b β k = 0 := by simp [hshape.1 k, hkp, hkq]
    exact hk hz
  have hqinv : (q : ι) ∈ leftRootInversionIndices b (simpleWeylWord b word) :=
    (root_mem_leftRootInversions b _ (q : ι)).mp
      (LeftRootInversion.triple_bond_short_simple_mem
        b word hword β hβroot p q hp hq hpq hqp hbad)
  have hqA : (q : ι) ∉ A := fun h =>
    (Set.disjoint_left.mp hA) h hqinv
  have hpos : ∀ γ ∈ s, b.IsPos γ := by
    intro γ hγ
    rcases hs.1 γ hγ with ha | hd
    · exact hApos γ ha
    · exact ((mem_leftRootInversionIndices b _ γ).mp (hD hd)).1
  obtain ⟨τ, hτs, hτD⟩ :=
    RootExpression.RootExpressionAuxiliaryOccurrence.exists_occurrence_of_distinct_word
      b word hword A D hD β hβ hβD s hs
  have hτA : τ ∈ A := (hs.1 τ hτs).resolve_right hτD
  have hτsupp : simpleRootSupportInt b τ ⊆ ({p, q} : Set b.support) :=
    (positiveRoot_summand_support_subset b s β hpos hs.2 τ hτs).trans hβsupp
  have hτp_le := positiveRoot_summand_coeff_le b s β hpos hs.2 τ hτs p
  have hτp_nonneg := simpleRootCoeffInt_nonneg_of_isPos b τ (hpos τ hτs) p
  have hτp : simpleRootCoeffInt b τ p = 1 := by
    by_contra hn
    have hz : simpleRootCoeffInt b τ p = 0 := by omega
    have heq := positive_tripleBond_zero_long_eq_short b p q hpq hqp τ
      (hpos τ hτs) hτsupp hz
    exact hqA (heq ▸ hτA)
  obtain ⟨t, hst⟩ := Multiset.exists_cons_of_mem hτs
  have hptotal := simpleRootCoeffInt_multiset_sum b s β hs.2 p
  rw [hst, Multiset.map_cons, Multiset.sum_cons, hβp, hτp] at hptotal
  have ht0 : (t.map (fun γ => simpleRootCoeffInt b γ p)).sum = 0 := by omega
  have htall : ∀ γ ∈ t, γ = (q : ι) := by
    intro γ hγt
    have hγs : γ ∈ s := hst ▸ (Multiset.mem_cons_of_mem hγt)
    have hγnonneg (δ : ℤ) (hδ : δ ∈ t.map (fun γ => simpleRootCoeffInt b γ p)) :
        0 ≤ δ := by
      obtain ⟨η, hη, rfl⟩ := Multiset.mem_map.mp hδ
      exact simpleRootCoeffInt_nonneg_of_isPos b η (hpos η (hst ▸
        Multiset.mem_cons_of_mem hη)) p
    have hγle : simpleRootCoeffInt b γ p ≤ 0 := by
      rw [← ht0]
      apply Multiset.single_le_sum hγnonneg
      exact Multiset.mem_map.mpr ⟨γ, hγt, rfl⟩
    have hγzero : simpleRootCoeffInt b γ p = 0 := by
      have := simpleRootCoeffInt_nonneg_of_isPos b γ (hpos γ hγs) p
      omega
    have hγsupp : simpleRootSupportInt b γ ⊆ ({p, q} : Set b.support) :=
      (positiveRoot_summand_support_subset b s β hpos hs.2 γ hγs).trans hβsupp
    exact positive_tripleBond_zero_long_eq_short b p q hpq hqp γ
      (hpos γ hγs) hγsupp hγzero
  let m := t.card
  have ht : t = Multiset.replicate m (q : ι) := Multiset.eq_replicate_card.mpr htall
  have hsform : s = {τ} + Multiset.replicate m (q : ι) := by
    rw [hst, ht]
    rfl
  have hmpos : 1 ≤ m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hsone : s = {τ} := by simpa [hm0] using hsform
    have hroot : P.root τ = P.root β := by
      simpa [hsone] using hs.2
    have hτβ : τ = β := P.root.injective hroot
    exact (Set.disjoint_left.mp hA) hτA (hτβ ▸ hβ)
  have hqD : (q : ι) ∈ D := by
    have hqs : (q : ι) ∈ s := by
      rw [hsform]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_replicate.mpr
        ⟨by omega, rfl⟩))
    exact (hs.1 (q : ι) hqs).resolve_left hqA
  have hqtotal := simpleRootCoeffInt_multiset_sum b s β hs.2 q
  rw [hsform, Multiset.map_add, Multiset.sum_add, hβq] at hqtotal
  have hτqnonneg := simpleRootCoeffInt_nonneg_of_isPos b τ (hpos τ hτs) q
  have hτq : simpleRootCoeffInt b τ q = 3 - m := by
    have hqsum : simpleRootCoeffInt b τ q + (m : ℤ) = 3 := by
      simpa [Multiset.map_replicate, Multiset.sum_replicate,
        simpleRootCoeffInt_simple, hpqne.symm] using hqtotal
    omega
  have hmle : m ≤ 3 := by omega
  exact ⟨τ, m, hτA, hqD, hmpos, hmle, hsform, hτp, hτq⟩

end ReductiveGroups
