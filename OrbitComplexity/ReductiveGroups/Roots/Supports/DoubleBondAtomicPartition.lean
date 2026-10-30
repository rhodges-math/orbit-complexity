import OrbitComplexity.ReductiveGroups.Roots.Inversions.RootExpressionForcedSummand
import OrbitComplexity.ReductiveGroups.Roots.Inversions.AmbientInversions

/-!
# Double-bond atomic partitions

Partitions of positive-root multisets on a double Cartan bond.
-/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- If two nonempty groups of original summands both sum to `γ`, and
the distinguished occurrence `τ` together with `γ` sums to a positive
root, minimal irreducibility compresses both groups to that same
single occurrence. -/
theorem RootExpression.MinimalIrreducible.double_partition_atomic
    (b : P.Base) (w : P.weylGroup)
    {A D : Set ι} {β τ γ δ : ι} {s r t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b w)
    (hmin : RootExpression.Minimal P A D β s)
    (hirr : RootExpression.Irreducible P b
      (leftRootInversionIndices b w) D s)
    (hs : s = {τ} + r + t) (hr : r ≠ 0) (ht : t ≠ 0)
    (hrsum : (r.map P.root).sum = P.root γ)
    (htsum : (t.map P.root).sum = P.root γ)
    (hγpos : b.IsPos γ) (hδpos : b.IsPos δ)
    (hδsum : P.root δ = P.root τ + P.root γ) :
    γ ∈ D ∧ r = {γ} ∧ t = {γ} ∧ s = {τ} + {γ} + {γ} := by
  have hpart : r + ({τ} + t) = s := by
    rw [hs]
    ac_rfl
  have hother : ({τ} + t).card ≥ 2 := by
    have htpos : 0 < t.card := Multiset.card_pos.mpr ht
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega
  have hotherne : ({τ} + t : Multiset ι) ≠ 0 := by
    intro he
    have hc := congrArg Multiset.card he
    simp only [Multiset.card_zero] at hc
    omega
  have hsumOther : (({τ} + t).map P.root).sum = P.root δ := by
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, htsum]
    exact hδsum.symm
  rcases RootExpression.MinimalIrreducible.inversion_cut_original_singleton
      b w hβ hmin hirr hpart hr hotherne hrsum hγpos
        hsumOther hδpos with h | h
  · have hγD : γ ∈ D := h.1
    have hrone : r = {γ} := h.2
    have hpart' : ({τ} + r) + t = s := by
      rw [hs]
    have htcard : t.card = 1 :=
      hmin.component_card_one hpart' ht htsum hγD
    have htone : t = {γ} :=
      rootExpression_component_eq_singleton htcard htsum
    exact ⟨hγD, hrone, htone, by rw [hs, hrone, htone]⟩
  · have hc : ({τ} + t).card = 1 := by rw [h.2]; rfl
    omega

variable [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Two inversions of one distinct-simple word cannot add to any
root, including when the two indices happen to coincide. -/
private theorem no_boolean_inversion_pair_root
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
    let n : V → ℕ := fun _ => 2
    have hv : P.root τ = P.root γ := congrArg Subtype.val hxy
    have hn : 2 ≤ ∑ z ∈ t, n z := by simp [t, n]
    have hroot : (∑ z ∈ t, n z • (z : M)) = P.root δ := by
      simp only [t, n, Finset.sum_singleton]
      change 2 • P.root τ = P.root δ
      rw [hsum, ← hv, two_nsmul]
    exact (inversion_natSum_not_root_ambient b word hword t n hn)
      ⟨δ, hroot.symm⟩
  · let t : Finset V := {x, y}
    let n : V → ℕ := fun _ => 1
    have hnot : x ∉ ({y} : Finset V) := by simpa using hxy
    have hn : 2 ≤ ∑ z ∈ t, n z := by
      simp [t, n, Finset.sum_insert hnot]
    have hroot : (∑ z ∈ t, n z • (z : M)) = P.root δ := by
      simpa only [t, n, Finset.sum_insert hnot, Finset.sum_singleton,
        one_nsmul, x, y] using hsum.symm
    exact (inversion_natSum_not_root_ambient b word hword t n hn)
      ⟨δ, hroot.symm⟩

/-- The original expression has exactly the atomic
configuration: two distinguished copies of `γ` and one auxiliary `τ`.
The classification of the remaining roots into the two `γ`-groups uses the
type-A interval partition; the two are combined in
`Roots/DoubleBondPrefixExpression.lean`. -/
theorem RootExpression.MinimalIrreducible.double_partition_atomic_auxiliary
    (b : P.Base) (word : List b.support) (hword : word.Nodup)
    {A D : Set ι} {β τ γ δ : ι} {s r t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b word))
    (hmin : RootExpression.Minimal P A D β s)
    (hirr : RootExpression.Irreducible P b
      (leftRootInversionIndices b (simpleWeylWord b word)) D s)
    (hs : s = {τ} + r + t) (hr : r ≠ 0) (ht : t ≠ 0)
    (hrsum : (r.map P.root).sum = P.root γ)
    (htsum : (t.map P.root).sum = P.root γ)
    (hγpos : b.IsPos γ) (hδpos : b.IsPos δ)
    (hδsum : P.root δ = P.root τ + P.root γ) :
    τ ∈ A ∧ γ ∈ D ∧ s = {τ} + {γ} + {γ} := by
  obtain ⟨hγD, _, _, hsform⟩ :=
    RootExpression.MinimalIrreducible.double_partition_atomic b
      (simpleWeylWord b word) hβ hmin hirr hs hr ht hrsum htsum
      hγpos hδpos hδsum
  have hτs : τ ∈ s := by
    rw [hsform]
    simp
  rcases hmin.1.1 τ hτs with hτA | hτD
  · exact ⟨hτA, hγD, hsform⟩
  · exact False.elim (no_boolean_inversion_pair_root b word hword
      (hD hτD) (hD hγD) hδsum)

end ReductiveGroups
