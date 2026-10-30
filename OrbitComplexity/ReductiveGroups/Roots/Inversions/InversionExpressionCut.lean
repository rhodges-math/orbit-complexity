import OrbitComplexity.ReductiveGroups.Roots.Supports.MinimalIrreducibleExpression
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionCone

/-!
# Inversion signs at a two-component root expression cut

The complement of the left inversion set is closed under positive-root
addition. This supplies the inversion-side premise at an expression cut
using the original Weyl action and root signs.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- If a positive inversion root is a sum of two positive roots,
at least one summand is an inversion. This is the coclosed half of the
usual inversion-set biclosedness statement. -/
theorem leftRootInversionIndices_add_coclosed
    (b : P.Base) (w : P.weylGroup) {β δ ε : ι}
    (hβ : β ∈ leftRootInversionIndices b w)
    (hδ : b.IsPos δ) (hε : b.IsPos ε)
    (hsum : P.root β = P.root δ + P.root ε) :
    δ ∈ leftRootInversionIndices b w ∨
      ε ∈ leftRootInversionIndices b w := by
  by_contra hn
  push Not at hn
  have hβ' := (mem_leftRootInversionIndices b w β).mp hβ
  have hδ' : b.IsPos (P.weylGroupToPerm w⁻¹ δ) := by
    by_contra hneg
    exact hn.1 ((mem_leftRootInversionIndices b w δ).mpr ⟨hδ, hneg⟩)
  have hε' : b.IsPos (P.weylGroupToPerm w⁻¹ ε) := by
    by_contra hneg
    exact hn.2 ((mem_leftRootInversionIndices b w ε).mpr ⟨hε, hneg⟩)
  have hsum' :
      P.root (P.weylGroupToPerm w⁻¹ β) =
        P.root (P.weylGroupToPerm w⁻¹ δ) +
          P.root (P.weylGroupToPerm w⁻¹ ε) := by
    simp only [← P.weylGroup_apply_root, hsum, smul_add]
  exact hβ'.2 (hδ'.add hε' hsum')

/-- The left-inversion cut criterion removes the abstract
`δ ∈ U ∨ ε ∈ U` premise from the minimal/irreducible expression lemma.
The two component sums must be positive roots. -/
theorem RootExpression.MinimalIrreducible.inversion_cut_singleton_side
    (b : P.Base) (w : P.weylGroup)
    {A D : Set ι} {β δ ε : ι} {l s t : Multiset ι}
    (hβ : β ∈ leftRootInversionIndices b w)
    (hmin : RootExpression.Minimal P A D β l)
    (hirr : RootExpression.Irreducible P b
      (leftRootInversionIndices b w) D l)
    (hpart : s + t = l) (hs : s ≠ 0) (ht : t ≠ 0)
    (hsum : (s.map P.root).sum = P.root δ) (hδpos : b.IsPos δ)
    (htsum : (t.map P.root).sum = P.root ε) (hεpos : b.IsPos ε) :
    (δ ∈ D ∧ s.card = 1) ∨ (ε ∈ D ∧ t.card = 1) := by
  have htotal : P.root β = P.root δ + P.root ε := by
    have h := hmin.1.2
    rw [← hpart, Multiset.map_add, Multiset.sum_add, hsum, htsum] at h
    exact h.symm
  exact RootExpression.MinimalIrreducible.singleton_side_of_cut b hmin hirr
    hpart hs ht hsum hδpos htsum hεpos
    (leftRootInversionIndices_add_coclosed b w hβ hδpos hεpos htotal)

end ReductiveGroups
