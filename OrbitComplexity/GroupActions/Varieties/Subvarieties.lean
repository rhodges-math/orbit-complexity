import OrbitComplexity.GroupActions.Varieties.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Closed subvarieties

Closed subsets of a variety carry the reduced induced scheme structure, obtained from their
vanishing ideal sheaf. This structure gives another variety over the same field.

## Main definitions

* `GroupActions.Variety.closedSubvariety`: the reduced induced variety on a closed subset.
* `GroupActions.Variety.closedInclusion`: the closed subvariety's inclusion.

## Main results

* `GroupActions.Variety.closedInclusion_range`: the inclusion has the prescribed closed image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K) (Z : Closeds X.scheme)

private theorem reduced_vanishing_subscheme :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have (U : X.scheme.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    have : _root_.IsReduced (Γ(X.scheme, U) ⧸ I.ideal U) := by
      apply (Ideal.isRadical_iff_quotient_reduced _).mp
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    change IsReduced (Spec (.of (Γ(X.scheme, U) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ I.subschemeCover.openCover this

/-- The reduced induced variety structure on a closed subset. -/
def closedSubvariety : GroupActions.Variety K where
  scheme := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  toSpec := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ X.toSpec
  reduced := reduced_vanishing_subscheme X Z

/-- The inclusion of a closed subvariety is a morphism over the base field. -/
def closedInclusion : (X.closedSubvariety Z).toOver ⟶ X.toOver :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

/-- The inclusion of a closed subvariety is a closed immersion. -/
instance closedInclusion_isClosedImmersion : IsClosedImmersion (X.closedInclusion Z).left :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

/-- The image of the closed-subvariety inclusion is the prescribed closed subset. -/
theorem closedInclusion_range :
    Set.range ((X.closedInclusion Z).left : (X.closedSubvariety Z).scheme → X.scheme) =
      (Z : Set X.scheme) := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X.scheme)
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

end

end GroupActions.Variety
