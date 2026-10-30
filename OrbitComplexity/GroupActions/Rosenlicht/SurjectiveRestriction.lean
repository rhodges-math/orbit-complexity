import OrbitComplexity.GroupActions.Varieties.Images
import OrbitComplexity.GroupActions.Varieties.RestrictedMorphisms

/-!
# Surjectivity over a target open subset

A dominant morphism of varieties is surjective over a nonempty open subset of its target.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

/-- A dominant morphism of varieties becomes surjective after restricting to
a nonempty open subset of its target. -/
theorem exists_surjective_restrict {K : Type u} [Field K]
    {X Y : GroupActions.Variety K} [Nonempty Y.scheme]
    (f : X.toOver ⟶ Y.toOver) [IsDominant f.left] :
    ∃ U : Y.scheme.Opens, (U : Set Y.scheme).Nonempty ∧
      Surjective (restrictHom f U).left := by
  let g : X.scheme ⟶ Y.scheme := f.left
  have : IsDominant g := inferInstanceAs (IsDominant f.left)
  have hr : IsConstructible (Set.range (g : X.scheme → Y.scheme)) := isConstructible_range f
  have hd : Dense (Set.range (g : X.scheme → Y.scheme)) := g.denseRange
  obtain ⟨U, hU, hne, hrange⟩ := GroupActions.exists_open_subset hr hd
  let V : Y.scheme.Opens := ⟨U, hU⟩
  refine ⟨V, hne, ⟨?_⟩⟩
  change Function.Surjective (g ∣_ V)
  intro y
  obtain ⟨x, hx⟩ := hrange y.property
  let z : g ⁻¹ᵁ V := ⟨x, by
    change g x ∈ U
    rw [hx]
    exact y.property⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact (morphismRestrict_base_coe g V z).trans hx

end

end GroupActions.Variety
