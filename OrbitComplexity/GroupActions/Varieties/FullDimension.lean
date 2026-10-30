import OrbitComplexity.GroupActions.Varieties.ImmersionDimension
import OrbitComplexity.GroupActions.Varieties.ClosedDimension

/-! # Immersions of full dimension

The closure of an integral immersed variety has the source dimension. In an irreducible
variety, a full-dimensional immersion is dominant. Reducedness then makes this dense
immersion an open immersion.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
namespace GroupActions.Variety
noncomputable section
universe u
variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- The closure of the image of an irreducible immersed variety has the source dimension. -/
theorem dim_closure_range_immersion (f : X.toOver ⟶ Y.toOver)
    [IsImmersion f.left] [IrreducibleSpace X.scheme] :
    topologicalKrullDim (closure (Set.range f.left)) = X.dim := by
  have h : topologicalKrullDim
      (closure ((f.left : X.scheme → Y.scheme) '' (Set.univ : Set X.scheme))) =
        topologicalKrullDim (closure (Set.univ : Set X.scheme)) :=
    dim_closure_image_immersion f Set.univ isOpen_univ.isLocallyClosed
      (IrreducibleSpace.isIrreducible_univ X.scheme)
  rw [Set.image_univ, closure_univ] at h
  exact h.trans (Homeomorph.Set.univ X.scheme).isHomeomorph.topologicalKrullDim_eq

/-- An immersion of equal-dimensional irreducible varieties is dominant. -/
theorem isDominant_of_dim_eq (f : X.toOver ⟶ Y.toOver) [IsImmersion f.left]
    [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme] (hdim : X.dim = Y.dim) :
    IsDominant f.left := by
  have hc : closure (Set.range f.left) = Set.univ :=
    Y.closed_eq_univ isClosed_closure ((dim_closure_range_immersion f).trans hdim)
  rw [isDominant_iff]
  exact dense_iff_closure_eq.mpr hc

/-- A dominant immersion into a reduced variety is an open immersion. -/
theorem isOpenImmersion_of_dominant (f : X.toOver ⟶ Y.toOver)
    [IsImmersion f.left] [IsDominant f.left] : IsOpenImmersion f.left := by
  let f₀ : X.scheme ⟶ Y.scheme := f.left
  have hco : (f₀.coborderRange : Set Y.scheme) = Set.range f₀ := by
    change coborder (Set.range f₀) = Set.range f₀
    rw [coborder_eq_union_closure_compl, f₀.denseRange.closure_eq, Set.compl_univ,
      Set.union_empty]
  have : Surjective f₀.liftCoborder := by
    constructor
    intro y
    have hy : f₀.coborderRange.ι y ∈ Set.range f₀ := hco ▸ y.property
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    apply f₀.coborderRange.ι.isEmbedding.injective
    exact (congrArg (fun g : X.scheme ⟶ Y.scheme => g x) f₀.liftCoborder_ι).trans hx
  have : IsIso f₀.liftCoborder := isIso_of_isClosedImmersion_of_surjective _
  have ho : IsOpenImmersion (f₀.liftCoborder ≫ f₀.coborderRange.ι) := inferInstance
  rwa [f₀.liftCoborder_ι] at ho

end
end GroupActions.Variety
