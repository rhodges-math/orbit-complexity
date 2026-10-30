import OrbitComplexity.GroupActions.Varieties.GenericFibres
import OrbitComplexity.GroupActions.Varieties.RestrictedFibres
import OrbitComplexity.GroupActions.Varieties.RestrictedMorphisms

/-! # Generic fibre dimension over an arbitrary variety

A nonempty affine open part of the target reduces the dimension formula to the affine
base case. Restriction preserves dimensions of the two varieties and of the whole fibres.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

/-- A dominant morphism of irreducible varieties satisfies the dimension formula
over a nonempty open subset of its target. -/
theorem exists_open_dim_add {K : Type u} [Field K] (X Y : GroupActions.Variety K)
    [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]
    (f : X.toOver ⟶ Y.toOver) [IsDominant f.left] :
    ∃ V : Y.scheme.Opens, (V : Set Y.scheme).Nonempty ∧ ∀ y ∈ V,
      X.dim = Y.dim + topologicalKrullDim (f.left.fiber y) := by
  let g : X.scheme ⟶ Y.scheme := f.left
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Y.scheme ∈ (⊤ : Y.scheme.Opens) from trivial)
  have hUne : (U : Set Y.scheme).Nonempty := ⟨_, hηU⟩
  have hXne : ((g ⁻¹ᵁ U) : Set X.scheme).Nonempty :=
    g.denseRange.exists_mem_open U.isOpen hUne
  let X' := X.openSubvariety (g ⁻¹ᵁ U)
  let Y' := Y.openSubvariety U
  have : Nonempty ((g ⁻¹ᵁ U) : Scheme) := ⟨⟨hXne.choose, hXne.choose_spec⟩⟩
  have : Nonempty (U : Scheme) := ⟨⟨hUne.choose, hUne.choose_spec⟩⟩
  have : IrreducibleSpace X'.scheme :=
    (g ⁻¹ᵁ U).ι.isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace Y'.scheme :=
    U.ι.isOpenEmbedding.irreducibleSpace
  have : IsAffine Y'.scheme := hU
  let f' := restrictHom f U
  obtain ⟨W, hW, hd⟩ := exists_open_dim_add_of_affine X' Y' f'
  refine ⟨U.ι ''ᵁ W, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hW
    exact ⟨U.ι z, U.ι.apply_mem_image_iff.mpr hz⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h := hd z hz
    change (X.openSubvariety (g ⁻¹ᵁ U)).dim = (Y.openSubvariety U).dim +
      topologicalKrullDim ((g ∣_ U).fiber z) at h
    rw [X.openSubvariety_dim (g ⁻¹ᵁ U) hXne, Y.openSubvariety_dim U hUne,
      fibre_dim_restrict g U z] at h
    exact h

end

end GroupActions.Variety
