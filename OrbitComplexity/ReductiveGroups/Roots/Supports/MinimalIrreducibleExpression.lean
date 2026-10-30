import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums
import Mathlib.Data.Multiset.Sum

/-!
# Minimal and irreducible root expressions

The multiset records occurrences, so repeated summands remain distinct.
The auxiliary and distinguished sets consist of root indices;
all equations are equations of the original root vectors.
-/

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- An admissible expression of the root `β`, allowing repeated
auxiliary or distinguished positive-root summands. -/
def RootExpression (P : RootPairing ι R M N)
    (A D : Set ι) (β : ι) (l : Multiset ι) : Prop :=
  (∀ γ ∈ l, γ ∈ A ∨ γ ∈ D) ∧ (l.map P.root).sum = P.root β

/-- Minimal cardinality among all expressions with the same
auxiliary and distinguished summand sets. -/
def RootExpression.Minimal (P : RootPairing ι R M N)
    (A D : Set ι) (β : ι) (l : Multiset ι) : Prop :=
  RootExpression P A D β l ∧
    ∀ l' : Multiset ι, RootExpression P A D β l' → l.card ≤ l'.card

/-- the `D`-irreducibility, tested on every nonempty
two-partition of the occurrence multiset whose sums are positive roots.
`U` is the inversion-root universe. -/
def RootExpression.Irreducible (P : RootPairing ι R M N)
    (b : P.Base) (U D : Set ι) (l : Multiset ι) : Prop :=
  ∀ (s t : Multiset ι) (δ ε : ι),
    s + t = l → s ≠ 0 → t ≠ 0 →
    (s.map P.root).sum = P.root δ → b.IsPos δ →
    (t.map P.root).sum = P.root ε → b.IsPos ε →
    (δ ∈ U → δ ∈ D) ∧ (ε ∈ U → ε ∈ D)

omit [CharZero R] in
/-- Compressing a component whose sum is a single distinguished root
would shorten a minimal expression unless that component has one
occurrence. This is the exact `D`-minimality step at an edge cut. -/
theorem RootExpression.Minimal.component_card_one
    {A D : Set ι} {β δ : ι} {l s t : Multiset ι}
    (hmin : RootExpression.Minimal P A D β l)
    (hpart : s + t = l) (ht : t ≠ 0)
    (hsum : (t.map P.root).sum = P.root δ) (hδ : δ ∈ D) :
    t.card = 1 := by
  classical
  have hnew : RootExpression P A D β (s + {δ}) := by
    constructor
    · intro γ hγ
      rcases Multiset.mem_add.mp hγ with hs | hsingle
      · exact hmin.1.1 γ (hpart ▸ (Multiset.mem_add.mpr (Or.inl hs)))
      · have he : γ = δ := by simpa using hsingle
        exact Or.inr (he ▸ hδ)
    · have htotal := hmin.1.2
      rw [← hpart, Multiset.map_add, Multiset.sum_add] at htotal
      simpa [Multiset.map_add, Multiset.sum_add, hsum] using htotal
  have hle := hmin.2 (s + {δ}) hnew
  rw [← hpart, Multiset.card_add, Multiset.card_add] at hle
  have hpos : 0 < t.card := Multiset.card_pos.mpr ht
  simp only [Multiset.card_singleton] at hle
  omega

/-- A positive-root two-cut of a minimal irreducible expression
has a singleton distinguished side whenever that side is in `U`.
For inversion sets, `δ ∈ U` or `ε ∈ U` is by
`leftRootInversionIndices_add_coclosed` (`Roots/InversionExpressionCut.lean`). -/
theorem RootExpression.MinimalIrreducible.singleton_side_of_cut
    (b : P.Base) {A U D : Set ι} {β δ ε : ι} {l s t : Multiset ι}
    (hmin : RootExpression.Minimal P A D β l)
    (hirr : RootExpression.Irreducible P b U D l)
    (hpart : s + t = l) (hs : s ≠ 0) (ht : t ≠ 0)
    (hsum : (s.map P.root).sum = P.root δ) (hδpos : b.IsPos δ)
    (htsum : (t.map P.root).sum = P.root ε) (hεpos : b.IsPos ε)
    (hU : δ ∈ U ∨ ε ∈ U) :
    (δ ∈ D ∧ s.card = 1) ∨ (ε ∈ D ∧ t.card = 1) := by
  have hD := hirr s t δ ε hpart hs ht hsum hδpos htsum hεpos
  rcases hU with hδU | hεU
  · have hδD := hD.1 hδU
    have hcard := hmin.component_card_one (s := t) (t := s)
      (by simpa [add_comm] using hpart) hs hsum hδD
    exact Or.inl ⟨hδD, hcard⟩
  · have hεD := hD.2 hεU
    exact Or.inr ⟨hεD, hmin.component_card_one hpart ht htsum hεD⟩

end ReductiveGroups
