import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Properties

/-! # Varieties over a field

A variety is a reduced separated scheme of finite type over a field. Its rational points
carry the topology induced from the scheme, and over an algebraically closed field they
identify with the closed points.

## Main definitions

* `GroupActions.Variety`: reduced separated schemes of finite type over a field.
* `GroupActions.Variety.points`: rational points as sections of the structure morphism.
* `GroupActions.Variety.pointMap`: the map from rational points to scheme points.

## Main results

* `GroupActions.Variety.pointMap_injective`: rational points are determined by their image.
* `GroupActions.Variety.pointMap_range`: rational points have precisely the closed points as image.

## Implementation notes

The scheme and base field belong to the same universe. The rational-point topology is induced
by evaluation at the unique point of the spectrum of the base field.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

/-- A reduced separated scheme of finite type over a field. -/
structure Variety (K : Type u) [Field K] where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the spectrum of the field. -/
  toSpec : scheme ⟶ Spec (CommRingCat.of K)
  /-- The underlying scheme is reduced. -/
  [reduced : IsReduced scheme]
  /-- The structure morphism is separated. -/
  [separated : IsSeparated toSpec]
  /-- The structure morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType toSpec]
  /-- The structure morphism is quasi-compact. -/
  [quasiCompact : QuasiCompact toSpec]

attribute [instance] Variety.reduced Variety.separated Variety.locallyOfFiniteType
  Variety.quasiCompact

namespace Variety

variable {K : Type u} [Field K] (X : Variety K)

/-- The scheme over the base field associated to a variety. -/
abbrev toOver : Over (Spec (CommRingCat.of K)) := Over.mk X.toSpec

/-- Rational points of a variety are sections of its structure morphism. -/
abbrev points :=
  {p : Spec (CommRingCat.of K) ⟶ X.scheme // p ≫ X.toSpec = 𝟙 _}

/-- The image of a rational point in the underlying scheme. -/
def pointMap (x : X.points) : X.scheme := x.val (IsLocalRing.closedPoint K)

/-- Rational points carry the topology induced from the underlying scheme. -/
instance pointsTopology : TopologicalSpace X.points :=
  TopologicalSpace.induced X.pointMap inferInstance

/-- Evaluation of rational points is continuous. -/
theorem continuous_pointMap : Continuous X.pointMap := continuous_induced_dom

variable [IsAlgClosed K]

/-- Rational points of a variety identify with its closed points. -/
noncomputable def pointsEquivClosedPoints : X.points ≃ closedPoints X.scheme :=
  pointEquivClosedPoint X.toSpec

/-- Rational points are determined by their images in the underlying scheme. -/
theorem pointMap_injective : Function.Injective X.pointMap := by
  intro x y h
  exact X.pointsEquivClosedPoints.injective (Subtype.ext h)

/-- Evaluation identifies rational points with a topological subspace of the scheme. -/
theorem isEmbedding_pointMap : IsEmbedding X.pointMap :=
  ⟨⟨rfl⟩, X.pointMap_injective⟩

/-- The images of rational points are precisely the closed points. -/
theorem pointMap_range : Set.range X.pointMap = closedPoints X.scheme := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (X.pointsEquivClosedPoints p).property
  · intro hx
    obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩

end Variety

end

end GroupActions
