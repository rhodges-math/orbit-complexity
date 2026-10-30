import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# TensorSchemeIso

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- A coefficient-algebra diagram isomorphism to a fixed-fibre diagram identifies
the corresponding scheme diagrams after forgetting their distinct bases. -/
noncomputable def tensorSchemeIso {J : Type v} [Category.{w} J]
    {S R M : Type u} [CommRing S] [CommRing R] [CommRing M]
    [Algebra S R] [Algebra R M] [Algebra S M] [IsScalarTower S R M]
    (G : J ⥤ CommAlgCat.{u} S) (D : J ⥤ CommAlgCat.{u} R)
    (iso : D ≅ fixedFibreDiagram (R := R) (M := M) G) :
    D.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)) ≅
      (fixedFibreDiagram (R := M) (M := M) G).op ⋙ algSpec (.of M) ⋙
        Over.forget (Spec (.of M)) :=
  Functor.isoWhiskerRight (NatIso.op iso.symm)
    (algSpec (.of R) ⋙ Over.forget (Spec (.of R)))

end FrobeniusSplitting
