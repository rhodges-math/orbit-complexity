import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.GroupActions.Varieties.Constructible

/-! # Open subsets of images

The image of a morphism from a nonempty variety contains a nonempty open subset of its
closure. Constructibility supplies the open subset.

## Main results

* `GroupActions.Variety.exists_open_inter_range`: an image contains a nonempty relatively
  open subset of its closure.

## References

* M. Brion, *Introduction to actions of algebraic groups*, Luminy lecture notes (2009),
  Proposition 1.11.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- The image of a nonempty variety contains a nonempty open part of its closure. -/
theorem exists_open_inter_range [Nonempty X.scheme] (f : X.toOver ⟶ Y.toOver) :
    ∃ U : Set Y.scheme, IsOpen U ∧
      (U ∩ closure (Set.range (f.left : X.scheme → Y.scheme))).Nonempty ∧
      U ∩ closure (Set.range (f.left : X.scheme → Y.scheme)) ⊆ Set.range f.left := by
  let g : X.scheme → Y.scheme := f.left
  have hg : Continuous g := f.left.continuous
  let C : Set Y.scheme := closure (Set.range g)
  have : Nonempty C := by
    obtain ⟨x⟩ : Nonempty X.scheme := inferInstance
    exact ⟨⟨g x, subset_closure ⟨x, rfl⟩⟩⟩
  have hC : IsClosedEmbedding (Subtype.val : C → Y.scheme) :=
    isClosed_closure.isClosedEmbedding_subtypeVal
  have hrange : IsConstructible (Set.range g) := isConstructible_range f
  have hconstruct : IsConstructible ((Subtype.val : C → Y.scheme) ⁻¹' Set.range g) :=
    hrange.preimage_of_isClosedEmbedding hC (NoetherianSpace.isCompact _)
  have hdense : Dense ((Subtype.val : C → Y.scheme) ⁻¹' Set.range g) := by
    apply Subtype.dense_iff.mpr
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    change C ⊆ closure (Set.range g ∩ C)
    rw [Set.inter_eq_left.mpr (show Set.range g ⊆ C from subset_closure)]
  obtain ⟨V, hV, hVne, hVrange⟩ := GroupActions.exists_open_subset hconstruct hdense
  obtain ⟨U, hU, hUV⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
  refine ⟨U, hU, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hVne
    refine ⟨x.val, ?_, x.property⟩
    change x ∈ (Subtype.val : C → Y.scheme) ⁻¹' U
    rw [hUV]
    exact hx
  · intro y hy
    have hmem : (⟨y, hy.2⟩ : C) ∈ V := by
      rw [← hUV]
      exact hy.1
    exact hVrange hmem

end GroupActions.Variety
