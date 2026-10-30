import OrbitComplexity.GroupActions.Varieties.Morphisms
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Open immersions on rational points

The rational-point image of a morphism is determined by its scheme image. Preimmersions
therefore induce embeddings on rational points, and open immersions induce open embeddings.

## Main results

* `GroupActions.Variety.range_mapPoints`: the rational image as a scheme-image inverse image.
* `GroupActions.Variety.isOpenEmbedding_mapPoints`: open embeddings on rational points.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : GroupActions.Variety K}

/-- The rational image is the inverse image of the scheme image under point evaluation. -/
theorem range_mapPoints (f : X.toOver ⟶ Y.toOver) :
    Set.range (mapPoints f) = Y.pointMap ⁻¹' Set.range (f.left : X.scheme → Y.scheme) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨X.pointMap x, rfl⟩
  · intro hy
    exact exists_mapPoints_eq f y hy

/-- A preimmersion of varieties induces an embedding on rational points. -/
theorem isEmbedding_mapPoints (f : X.toOver ⟶ Y.toOver) [IsPreimmersion f.left] :
    IsEmbedding (mapPoints f) := by
  have he : IsEmbedding (Y.pointMap ∘ mapPoints f) := by
    change IsEmbedding ((f.left : X.scheme → Y.scheme) ∘ X.pointMap)
    exact f.left.isEmbedding.comp X.isEmbedding_pointMap
  exact Y.isEmbedding_pointMap.of_comp_iff.mp he

/-- An open immersion of varieties induces an open embedding on rational points. -/
theorem isOpenEmbedding_mapPoints (f : X.toOver ⟶ Y.toOver) [IsOpenImmersion f.left] :
    IsOpenEmbedding (mapPoints f) := by
  refine ⟨isEmbedding_mapPoints f, ?_⟩
  rw [range_mapPoints]
  exact f.left.isOpenEmbedding.isOpen_range.preimage Y.continuous_pointMap

end

end GroupActions.Variety
