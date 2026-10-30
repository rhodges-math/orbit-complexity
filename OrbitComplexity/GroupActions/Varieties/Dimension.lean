import OrbitComplexity.GroupActions.Varieties.Morphisms
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-! # Dimensions of varieties and sets of rational points

The dimension of a variety is the Krull dimension of its scheme. The dimension of a set of
rational points is the dimension of its closure in that scheme.

## Main definitions

* `GroupActions.Variety.dim`: the Krull dimension of the underlying scheme.
* `GroupActions.Variety.pointClosure`: the scheme closure of a set of rational points.
* `GroupActions.Variety.subsetDim`: dimension of a set of rational points.

## Main results

* `GroupActions.Variety.subsetDim_mono`: dimension is monotone under inclusion.
* `GroupActions.Variety.open_dim`: a nonempty open subset of an irreducible variety has the
  variety's dimension.

## Implementation notes

Dimensions take values in `WithBot ℕ∞`, with the empty set of dimension bottom.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

/-- The dimension of a variety is the Krull dimension of its underlying scheme. -/
noncomputable def dim : WithBot ℕ∞ := topologicalKrullDim X.scheme

/-- The closure of a set of rational points in the underlying scheme. -/
def pointClosure (S : Set X.points) : Set X.scheme := closure (X.pointMap '' S)

/-- The dimension of a set of rational points is the dimension of its scheme closure. -/
noncomputable def subsetDim (S : Set X.points) : WithBot ℕ∞ :=
  topologicalKrullDim (X.pointClosure S)

/-- Inclusion of sets of rational points implies inclusion of their scheme closures. -/
theorem pointClosure_mono {S T : Set X.points} (h : S ⊆ T) :
    X.pointClosure S ⊆ X.pointClosure T := closure_mono (Set.image_mono h)

/-- The dimension of sets of rational points is monotone under inclusion. -/
theorem subsetDim_mono {S T : Set X.points} (h : S ⊆ T) : X.subsetDim S ≤ X.subsetDim T :=
  (IsEmbedding.inclusion (X.pointClosure_mono h)).isInducing.topologicalKrullDim_le

/-- A set of rational points has dimension at most its ambient variety. -/
theorem subsetDim_le (S : Set X.points) : X.subsetDim S ≤ X.dim :=
  topologicalKrullDim_subspace_le X.scheme (X.pointClosure S)

/-- Isomorphic varieties have equal dimensions. -/
theorem dim_eq_of_iso {Y : GroupActions.Variety K} (e : X.toOver ≅ Y.toOver) :
    X.dim = Y.dim :=
  ((Over.forget _).mapIso e).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

/-- The closure of a set of rational points commutes with a variety isomorphism. -/
theorem pointClosure_image {Y : GroupActions.Variety K} (e : X.toOver ≅ Y.toOver)
    (S : Set X.points) : Y.pointClosure (mapPoints e.hom '' S) =
      e.hom.left '' X.pointClosure S := by
  let h := ((Over.forget _).mapIso e).hom.homeomorph
  calc
    Y.pointClosure (mapPoints e.hom '' S) =
        closure (e.hom.left '' (X.pointMap '' S)) := by
      simp only [pointClosure, Set.image_image, pointMap_mapPoints]
    _ = e.hom.left '' X.pointClosure S := (h.image_closure (X.pointMap '' S)).symm

/-- A nonempty open subset of an irreducible variety has the dimension of the variety. -/
theorem open_dim [IrreducibleSpace X.scheme] (U : X.scheme.Opens)
    (hU : (U : Set X.scheme).Nonempty) :
    topologicalKrullDim U = X.dim := by
  have hdim :=
    TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType X.toSpec
      (IrreducibleSpace.isIrreducible_univ X.scheme) isClosed_univ U.isOpen
      (by simpa only [Set.univ_inter] using hU)
  rw [Set.univ_inter] at hdim
  exact hdim.trans (Homeomorph.Set.univ X.scheme).isHomeomorph.topologicalKrullDim_eq

variable [IsAlgClosed K]

/-- Rational points are dense in the underlying scheme. -/
theorem pointClosure_univ : X.pointClosure Set.univ = Set.univ := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  rw [pointClosure, Set.image_univ, X.pointMap_range, closure_closedPoints]

/-- The closure of the rational image of a morphism equals the closure of its scheme image. -/
theorem pointClosure_range {Y : GroupActions.Variety K} (f : X.toOver ⟶ Y.toOver) :
    Y.pointClosure (Set.range (mapPoints f)) =
      closure (Set.range (f.left : X.scheme → Y.scheme)) := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  change closure (Y.pointMap '' Set.range (mapPoints f)) = _
  rw [← Set.range_comp]
  change closure (Set.range ((f.left : X.scheme → Y.scheme) ∘ X.pointMap)) = _
  rw [Set.range_comp]
  let g : X.scheme → Y.scheme := f.left
  have hg : Continuous g := f.left.continuous
  change closure (g '' Set.range X.pointMap) = closure (Set.range g)
  have h := closure_image_closure (f := g) (s := Set.range X.pointMap) hg
  rw [X.pointMap_range, closure_closedPoints, Set.image_univ] at h
  rw [X.pointMap_range]
  exact h.symm

end

end GroupActions.Variety
