import OrbitComplexity.GroupActions.Varieties.Dimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Closed images containing a dense rational image

The rational image of a dense variety morphism is scheme-dense over an algebraically closed
field. A universally closed morphism whose image contains those points is therefore surjective.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A universally closed image containing a dense rational image is the whole target. -/
theorem surjective_of_dense_points (Y C : GroupActions.Variety K) {X : Scheme.{u}}
    (f : X ⟶ Y.scheme) [UniversallyClosed f] (j : C.toOver ⟶ Y.toOver)
    (hj : DenseRange (j.left : C.scheme → Y.scheme))
    (hpoints : ∀ p : C.points,
      Y.pointMap (mapPoints j p) ∈ Set.range (f : X → Y.scheme)) : Surjective f := by
  have hclosed : IsClosed (Set.range (f : X → Y.scheme)) := f.isClosedMap.isClosed_range
  have hsub : Y.pointClosure (Set.range (mapPoints j)) ⊆
      Set.range (f : X → Y.scheme) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact hpoints p
  have huniv : Set.univ ⊆ Set.range (f : X → Y.scheme) := by
    simpa only [C.pointClosure_range j, hj.closure_range] using hsub
  rw [surjective_iff, ← Set.range_eq_univ]
  exact Set.Subset.antisymm (Set.subset_univ _) huniv

end GroupActions.Variety
