import OrbitComplexity.GroupActions.Rosenlicht.AffineSchemePoints
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-!
# AffineOpenPoints
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

/-- A rational point of an affine open chart evaluates its regular sections
in the base field. -/
def affineOpenPointEval (U : X.scheme.Opens) (hU : IsAffineOpen U)
    (p : (X.openSubvariety U).points) : Γ(X.scheme, U) →+* K :=
  letI : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X.toSpec⟩
  letI : IsAffine U.toScheme := hU
  letI : Algebra K Γ(U.toScheme, ⊤) := chartCoordinateAlgebra (.of K) U.toScheme
  ((affineSchemePointsEquiv K U.toScheme) p).toRingHom.comp U.topIso.inv.hom

end

end GroupActions.Variety
