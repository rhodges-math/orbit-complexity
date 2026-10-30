import OrbitComplexity.GroupActions.Varieties.LocallyClosedVarieties
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Image dimensions under immersions

An immersion preserves the dimension of the closure of an irreducible locally closed set.
The same holds for rational images of variety morphisms whose scheme images have these
properties.

## Main results

* `GroupActions.Variety.dim_closure_image_immersion`: closure dimension under an immersion.
* `GroupActions.Variety.subsetDim_range_immersion`: dimension of a rational morphism image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- Immersing an irreducible locally closed set preserves its closure dimension. -/
theorem dim_closure_image_immersion (f : X.toOver ⟶ Y.toOver) [IsImmersion f.left]
    (S : Set X.scheme) (hS : IsLocallyClosed S) (hI : IsIrreducible S) :
    topologicalKrullDim (closure (f.left '' S)) = topologicalKrullDim (closure S) := by
  have hSI : IsLocallyClosed (f.left '' S) :=
    hS.image f.left.isEmbedding.isInducing f.left.isLocallyClosed_range
  have hII : IsIrreducible (f.left '' S) := hI.image f.left f.left.continuous.continuousOn
  let e : S ≃ₜ f.left '' S :=
    (f.left.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
      (.setCongr (by
        simp only [Set.range_comp, Subtype.range_coe_subtype]
        rfl))
  have hdimX : topologicalKrullDim S = topologicalKrullDim (closure S) :=
    (X.locallyClosedHomeomorph S hS).isHomeomorph.topologicalKrullDim_eq.symm.trans
      (X.locallyClosedSubvariety_dim S hS hI)
  have hdimY : topologicalKrullDim (f.left '' S) =
      topologicalKrullDim (closure (f.left '' S)) :=
    (Y.locallyClosedHomeomorph (f.left '' S) hSI).isHomeomorph.topologicalKrullDim_eq.symm.trans
      (Y.locallyClosedSubvariety_dim (f.left '' S) hSI hII)
  exact hdimY.symm.trans (e.isHomeomorph.topologicalKrullDim_eq.symm.trans hdimX)

variable [IsAlgClosed K] {Z : GroupActions.Variety K}

/-- An immersion preserves the dimension of an irreducible locally closed rational image. -/
theorem subsetDim_range_immersion (f : Z.toOver ⟶ X.toOver) (g : X.toOver ⟶ Y.toOver)
    [IsImmersion g.left]
    (hS : IsLocallyClosed (Set.range (f.left : Z.scheme → X.scheme)))
    (hI : IsIrreducible (Set.range (f.left : Z.scheme → X.scheme))) :
    Y.subsetDim (Set.range (mapPoints (f ≫ g))) = X.subsetDim (Set.range (mapPoints f)) := by
  unfold subsetDim
  rw [Z.pointClosure_range (f ≫ g), Z.pointClosure_range f]
  change topologicalKrullDim (closure (Set.range
    ((g.left : X.scheme → Y.scheme) ∘ (f.left : Z.scheme → X.scheme)))) =
      topologicalKrullDim (closure (Set.range (f.left : Z.scheme → X.scheme)))
  rw [Set.range_comp]
  exact dim_closure_image_immersion g _ hS hI

end

end GroupActions.Variety
