import OrbitComplexity.GroupActions.Varieties.FiniteDimension

/-! # Dimension of proper closed subsets

A proper closed subset of a finite dimensional irreducible variety has smaller dimension.
The proof appends the whole variety to every chain of irreducible closed subsets.

## Main results

* `GroupActions.Variety.closed_dim_lt`: proper closed subsets have smaller dimension.
* `GroupActions.Variety.closed_eq_univ`: a closed subset of full dimension is the whole variety.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open TopologicalSpace.IrreducibleCloseds

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K)
  [IrreducibleSpace X.scheme]

/-- A proper closed subset of an irreducible variety has strictly smaller dimension. -/
theorem closed_dim_lt {C : Set X.scheme} (hC : IsClosed C) (hproper : C ≠ Set.univ) :
    topologicalKrullDim C < X.dim := by
  by_cases hbot : topologicalKrullDim C = ⊥
  · rw [hbot]
    exact bot_lt_iff_ne_bot.mpr X.dim_ne_bot
  have : Nonempty (IrreducibleCloseds C) := Order.krullDim_ne_bot_iff.mp hbot
  let whole : IrreducibleCloseds X.scheme :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.scheme, isClosed_univ⟩
  let f : WithTop (IrreducibleCloseds C) → IrreducibleCloseds X.scheme :=
    WithTop.recTopCoe whole (map (Subtype.val : C → X.scheme) continuous_subtype_val)
  have hf : StrictMono f := by
    apply WithTop.strictMono_iff.mpr
    refine ⟨map_strictMono_of_isInducing IsInducing.subtypeVal, ?_⟩
    intro Z
    apply lt_of_le_of_ne (show f Z ≤ whole from Set.subset_univ _)
    intro heq
    have hsub : (f Z : Set X.scheme) ⊆ C := by
      apply closure_minimal _ hC
      rintro p ⟨q, _, rfl⟩
      exact q.property
    have hwhole : Set.univ ⊆ C := by
      change (whole : Set X.scheme) ⊆ C
      rw [← heq]
      exact hsub
    exact hproper (Set.Subset.antisymm (Set.subset_univ C) hwhole)
  have hdim : topologicalKrullDim C + 1 ≤ X.dim := by
    have h := Order.krullDim_le_of_strictMono f hf
    rw [Order.krullDim_WithTop] at h
    exact h
  have htop : topologicalKrullDim C ≠ ⊤ := by
    intro h
    apply X.dim_ne_top
    exact top_le_iff.mp (h ▸ topologicalKrullDim_subspace_le X.scheme C)
  let n : ℕ := ((topologicalKrullDim C).unbotD 0).toNat
  have hn : (n : WithBot ℕ∞) = topologicalKrullDim C :=
    natCast_unbotD_toNat _ hbot htop
  apply lt_of_lt_of_le _ hdim
  rw [← hn]
  exact_mod_cast Nat.lt_succ_self n

/-- A closed subset of full dimension in an irreducible variety is the whole variety. -/
theorem closed_eq_univ {C : Set X.scheme} (hC : IsClosed C)
    (hdim : topologicalKrullDim C = X.dim) : C = Set.univ := by
  by_contra hproper
  exact (X.closed_dim_lt hC hproper).ne hdim

end

end GroupActions.Variety
