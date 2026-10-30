import OrbitComplexity.ReductiveGroups.Roots.Supports.MultiplicityFreeSupportPartition
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Positive Root Summand Bounds

Coefficient and support bounds for each original occurrence in an
arbitrary positive-root sum.  -/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The equality is

```lean
(s.map (fun γ => simpleRootCoeffInt b γ i)).sum = simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_multiset_sum (b : P.Base) (s : Multiset ι) (β : ι)
    (hsum : (s.map P.root).sum = P.root β) (i : b.support) :
    (s.map (fun γ => simpleRootCoeffInt b γ i)).sum = simpleRootCoeffInt b β i := by
  induction s using Quotient.inductionOn with
  | h l =>
    exact simpleRootCoeffInt_list_sum b l β hsum i

/-- The inclusion is

```lean
simpleRootCoeffInt b γ i ≤ simpleRootCoeffInt b β i
```
-/
theorem positiveRoot_summand_coeff_le (b : P.Base) (s : Multiset ι) (β : ι)
    (hpos : ∀ γ ∈ s, b.IsPos γ)
    (hsum : (s.map P.root).sum = P.root β)
    (γ : ι) (hγ : γ ∈ s) (i : b.support) :
    simpleRootCoeffInt b γ i ≤ simpleRootCoeffInt b β i := by
  rw [← simpleRootCoeffInt_multiset_sum b s β hsum i]
  apply Multiset.single_le_sum
  · intro c hc
    obtain ⟨δ, hδ, rfl⟩ := Multiset.mem_map.mp hc
    exact simpleRootCoeffInt_nonneg_of_isPos b δ (hpos δ hδ) i
  · exact Multiset.mem_map.mpr ⟨γ, hγ, rfl⟩

/-- The inclusion is

```lean
simpleRootSupportInt b γ ⊆ simpleRootSupportInt b β
```
-/
theorem positiveRoot_summand_support_subset (b : P.Base) (s : Multiset ι) (β : ι)
    (hpos : ∀ γ ∈ s, b.IsPos γ)
    (hsum : (s.map P.root).sum = P.root β)
    (γ : ι) (hγ : γ ∈ s) : simpleRootSupportInt b γ ⊆ simpleRootSupportInt b β := by
  intro i hi
  have hle := positiveRoot_summand_coeff_le b s β hpos hsum γ hγ i
  have hnonneg := simpleRootCoeffInt_nonneg_of_isPos b γ (hpos γ hγ) i
  change simpleRootCoeffInt b γ i ≠ 0 at hi
  change simpleRootCoeffInt b β i ≠ 0
  omega

end ReductiveGroups
