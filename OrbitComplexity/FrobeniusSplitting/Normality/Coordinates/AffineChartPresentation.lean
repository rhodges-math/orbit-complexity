import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Finite presentation of affine chart sections

The finite-presentation certificate for a structural map gives the
corresponding certificate for its ring of sections with the prescribed
coefficient action.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

open private coordinates_finitePresentation from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

namespace FrobeniusSplitting

/-- The section ring of an affine scheme is finitely presented for the
coefficient action induced by its structural map. -/
theorem finitePresentation_chartSections {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] :
    let : Algebra R Γ(X, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    Algebra.FinitePresentation R Γ(X, ⊤) := by
  exact @coordinates_finitePresentation (.of R) (Over.mk f)
    (show IsAffine (Over.mk f).left from ‹IsAffine X›)
    (show LocallyOfFinitePresentation (Over.mk f).hom from
      ‹LocallyOfFinitePresentation f›)

end FrobeniusSplitting
