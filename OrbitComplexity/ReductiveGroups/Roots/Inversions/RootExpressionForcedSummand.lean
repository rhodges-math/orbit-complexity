import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionExpressionCut

/-!
# Root Expression Forced Summand

the forced distinguished-summand lemma for a positive-root
partition. The multiset equality identifies an original occurrence, and
does not impose multiplicity-free simple coordinates. -/

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

omit [CharZero R] in
/-- The equality is

```lean
s = {δ}
```
-/
theorem rootExpression_component_eq_singleton {s : Multiset ι} {δ : ι}
    (hcard : s.card = 1) (hsum : (s.map P.root).sum = P.root δ) :
    s = {δ} := by
  obtain ⟨ε, rfl⟩ := Multiset.card_eq_one.mp hcard
  have heq : ε = δ := P.root.injective (by simpa using hsum)
  simp [heq]

/-- Every positive-root two-partition has a part that is a single original
distinguished summand. This identifies the occurrence multiset itself. -/
theorem RootExpression.MinimalIrreducible.inversion_cut_original_singleton
    (b : P.Base) (w : P.weylGroup)
    {A D : Set ι} {β δ ε : ι} {l s t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b w)
    (hmin : RootExpression.Minimal P A D β l)
    (hirr : RootExpression.Irreducible P b (leftRootInversionIndices b w) D l)
    (hpart : s + t = l) (hs : s ≠ 0) (ht : t ≠ 0)
    (hsum : (s.map P.root).sum = P.root δ) (hδpos : b.IsPos δ)
    (htsum : (t.map P.root).sum = P.root ε) (hεpos : b.IsPos ε) :
    (δ ∈ D ∧ s = {δ}) ∨ (ε ∈ D ∧ t = {ε}) := by
  rcases RootExpression.MinimalIrreducible.inversion_cut_singleton_side
    b w hβ hmin hirr hpart hs ht hsum hδpos htsum hεpos with h | h
  · exact Or.inl ⟨h.1, rootExpression_component_eq_singleton h.2 hsum⟩
  · exact Or.inr ⟨h.1, rootExpression_component_eq_singleton h.2 htsum⟩

/-- If one component sum is not any original distinguished summand,
the opposite component is exactly one distinguished occurrence. -/
theorem RootExpression.MinimalIrreducible.forced_distinguished_opposite
    (b : P.Base) (w : P.weylGroup)
    {A D : Set ι} {β δ ε : ι} {l s t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b w)
    (hmin : RootExpression.Minimal P A D β l)
    (hirr : RootExpression.Irreducible P b (leftRootInversionIndices b w) D l)
    (hpart : s + t = l) (hs : s ≠ 0) (ht : t ≠ 0)
    (hsum : (s.map P.root).sum = P.root δ) (hδpos : b.IsPos δ)
    (htsum : (t.map P.root).sum = P.root ε) (hεpos : b.IsPos ε)
    (hnot : ¬ (ε ∈ l ∧ ε ∈ D)) :
    δ ∈ D ∧ s = {δ} := by
  rcases RootExpression.MinimalIrreducible.inversion_cut_original_singleton
    b w hβ hmin hirr hpart hs ht hsum hδpos htsum hεpos with h | h
  · exact h
  · have hmem : ε ∈ l := by
      rw [← hpart, h.2]
      exact Multiset.mem_add.mpr (Or.inr (by simp))
    exact False.elim (hnot ⟨hmem, h.1⟩)

end ReductiveGroups
