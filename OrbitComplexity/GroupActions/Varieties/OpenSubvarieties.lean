import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.GroupActions.Varieties.Dimension

/-! # Open subvarieties

Every open subset of a variety over a field is another variety. Finite type is preserved
because the underlying scheme is Noetherian.

## Main definitions

* `GroupActions.Variety.openSubvariety`: the variety on an open subset.
* `GroupActions.Variety.openInclusion`: its inclusion into the ambient variety.

## Main results

* `GroupActions.Variety.openInclusion_range`: the inclusion has the prescribed open image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K) (U : X.scheme.Opens)

/-- The induced variety structure on an open subset. -/
def openSubvariety : GroupActions.Variety K where
  scheme := U
  toSpec := U.ι ≫ X.toSpec

/-- The inclusion of an open subvariety is a morphism over the base field. -/
def openInclusion : (X.openSubvariety U).toOver ⟶ X.toOver := Over.homMk U.ι

/-- The inclusion of an open subvariety is an open immersion. -/
instance openInclusion_isOpenImmersion : IsOpenImmersion (X.openInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The image of the open-subvariety inclusion is the prescribed open subset. -/
theorem openInclusion_range :
    Set.range ((X.openInclusion U).left : (X.openSubvariety U).scheme → X.scheme) =
      (U : Set X.scheme) := Scheme.Opens.range_ι U

/-- A nonempty open subvariety of an irreducible variety has the ambient dimension. -/
theorem openSubvariety_dim [IrreducibleSpace X.scheme] (hne : (U : Set X.scheme).Nonempty) :
    (X.openSubvariety U).dim = X.dim := X.open_dim U hne

end

end GroupActions.Variety
