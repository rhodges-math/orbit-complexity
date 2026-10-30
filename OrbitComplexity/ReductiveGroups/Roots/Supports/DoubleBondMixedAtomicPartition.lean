import OrbitComplexity.ReductiveGroups.Roots.Supports.DoubleBondAtomicPartition

/-!
# Double Bond Mixed Atomic Partition

Occurrence compression in the two-distinct-tail-root case. -/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Two roots in the inversion set of a distinct-simple word cannot
sum to any root. Coincident indices are covered by the multiplicity-two branch. -/
theorem boolean_inversion_pair_not_root
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    {τ γ δ : ι}
    (hτ : τ ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hγ : γ ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hsum : P.root δ = P.root τ + P.root γ) : False := by
  classical
  let V : Set M := leftRootInversions b (simpleWeylWord b word)
  let x : V := ⟨P.root τ, ⟨τ, hτ, rfl⟩⟩
  let y : V := ⟨P.root γ, ⟨γ, hγ, rfl⟩⟩
  by_cases hxy : x = y
  · let t : Finset V := {x}
    let mult : V → ℕ := fun _ => 2
    have hv : P.root τ = P.root γ := congrArg Subtype.val hxy
    have hn : 2 ≤ ∑ z ∈ t, mult z := by simp [t, mult]
    have hroot : (∑ z ∈ t, mult z • (z : M)) = P.root δ := by
      simp only [t, mult, Finset.sum_singleton]
      change 2 • P.root τ = P.root δ
      rw [hsum, ← hv, two_nsmul]
    exact (inversion_natSum_not_root_ambient b word hword t mult hn)
      ⟨δ, hroot.symm⟩
  · let t : Finset V := {x, y}
    let mult : V → ℕ := fun _ => 1
    have hnot : x ∉ ({y} : Finset V) := by simpa using hxy
    have hn : 2 ≤ ∑ z ∈ t, mult z := by
      simp [t, mult, Finset.sum_insert hnot]
    have hroot : (∑ z ∈ t, mult z • (z : M)) = P.root δ := by
      simpa only [t, mult, Finset.sum_insert hnot, Finset.sum_singleton,
        one_nsmul, x, y] using hsum.symm
    exact (inversion_natSum_not_root_ambient b word hword t mult hn)
      ⟨δ, hroot.symm⟩

/-- Both original groups of summands are forced to be singleton
distinguished occurrences by the two positive-root cuts. The
remaining original occurrence is auxiliary. -/
theorem RootExpression.MinimalIrreducible.mixed_partition_atomic_auxiliary
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    {A D : Set ι} {β τ γ₁ γ₂ δ₁ δ₂ : ι} {s r t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b word))
    (hmin : RootExpression.Minimal P A D β s)
    (hirr : RootExpression.Irreducible P b
      (leftRootInversionIndices b (simpleWeylWord b word)) D s)
    (hs : s = {τ} + r + t) (hr : r ≠ 0) (ht : t ≠ 0)
    (hrsum : (r.map P.root).sum = P.root γ₁)
    (htsum : (t.map P.root).sum = P.root γ₂)
    (hγ₁pos : b.IsPos γ₁) (hγ₂pos : b.IsPos γ₂)
    (hδ₁pos : b.IsPos δ₁) (hδ₂pos : b.IsPos δ₂)
    (hδ₁sum : P.root δ₁ = P.root τ + P.root γ₁)
    (hδ₂sum : P.root δ₂ = P.root τ + P.root γ₂) :
    τ ∈ A ∧ γ₁ ∈ D ∧ γ₂ ∈ D ∧
      r = {γ₁} ∧ t = {γ₂} ∧ s = {τ} + {γ₁} + {γ₂} := by
  have hpart₁ : r + ({τ} + t) = s := by rw [hs]; ac_rfl
  have hother₁ : 2 ≤ ({τ} + t : Multiset ι).card := by
    have htpos : 0 < t.card := Multiset.card_pos.mpr ht
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega
  have hother₁ne : ({τ} + t : Multiset ι) ≠ 0 := by
    intro he
    have hc := congrArg Multiset.card he
    simp only [Multiset.card_zero] at hc
    omega
  have hsumOther₁ : (({τ} + t).map P.root).sum = P.root δ₂ := by
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, htsum]
    exact hδ₂sum.symm
  have hcut₁ := RootExpression.MinimalIrreducible.inversion_cut_original_singleton
    b (simpleWeylWord b word) hβ hmin hirr hpart₁ hr hother₁ne
      hrsum hγ₁pos hsumOther₁ hδ₂pos
  have hfirst : γ₁ ∈ D ∧ r = {γ₁} := by
    rcases hcut₁ with h | h
    · exact h
    · have hc : ({τ} + t : Multiset ι).card = 1 := by rw [h.2]; rfl
      omega
  have hpart₂ : t + ({τ} + r) = s := by rw [hs]; ac_rfl
  have hother₂ : 2 ≤ ({τ} + r : Multiset ι).card := by
    have hrpos : 0 < r.card := Multiset.card_pos.mpr hr
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega
  have hother₂ne : ({τ} + r : Multiset ι) ≠ 0 := by
    intro he
    have hc := congrArg Multiset.card he
    simp only [Multiset.card_zero] at hc
    omega
  have hsumOther₂ : (({τ} + r).map P.root).sum = P.root δ₁ := by
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, hrsum]
    exact hδ₁sum.symm
  have hcut₂ := RootExpression.MinimalIrreducible.inversion_cut_original_singleton
    b (simpleWeylWord b word) hβ hmin hirr hpart₂ ht hother₂ne
      htsum hγ₂pos hsumOther₂ hδ₁pos
  have hsecond : γ₂ ∈ D ∧ t = {γ₂} := by
    rcases hcut₂ with h | h
    · exact h
    · have hc : ({τ} + r : Multiset ι).card = 1 := by rw [h.2]; rfl
      omega
  have hsform : s = {τ} + {γ₁} + {γ₂} := by
    rw [hs, hfirst.2, hsecond.2]
  have hτs : τ ∈ s := by rw [hsform]; simp
  have hτA : τ ∈ A := by
    rcases hmin.1.1 τ hτs with h | h
    · exact h
    · exact False.elim (boolean_inversion_pair_not_root b word hword
        (hD h) (hD hfirst.1) hδ₁sum)
  exact ⟨hτA, hfirst.1, hsecond.1,
    hfirst.2, hsecond.2, hsform⟩

end ReductiveGroups
