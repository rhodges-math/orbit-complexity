import OrbitComplexity.GroupActions.Rosenlicht.TensorDomains
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Integral affine products

An integral affine scheme of finite type over an algebraically closed field is
geometrically integral. Its product with an integral locally noetherian scheme
over the same field is therefore integral.

## Main results

* `geometricallyIntegral_affine`: an integral affine algebra gives a geometrically integral scheme.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

universe u

private instance integral_isoClosed :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
  ⟨fun e h ↦ by
    have : IsIntegral _ := h
    exact IsIntegral.of_isIso e.hom⟩

variable {K A : Type u} [Field K] [IsAlgClosed K]
variable [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsDomain A]

/-- An integral affine scheme of finite type over an algebraically closed field is
geometrically integral over that field. -/
theorem geometricallyIntegral_affine :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral) (R := K)
    (f := Spec.map (CommRingCat.ofHom (algebraMap K A)))).mpr
  intro L _ _
  have : IsDomain (A ⊗[K] L) := isDomain_tensorProduct
  exact IsIntegral.of_isIso (pullbackSpecIso (CommRingCat.of K)
    (CommRingCat.of A) (CommRingCat.of L)).inv

end

end GroupActions
