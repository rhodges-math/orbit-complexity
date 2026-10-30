import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.FiniteStability

/-!
# ScalarImageProperties

Arithmetic coefficient models and compatible chart comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- Flat initial models embed into a generic scalar-extension comparison over any
intermediate coefficient ring that embeds in the generic coefficient ring. -/
theorem scalarImageHom_injective [Module.Flat S M]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (scalarImageHom (R := R) e) := by
  let f : R →ₐ[S] K := IsScalarTower.toAlgHom S R K
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (Algebra.ofId R K) (AlgHom.id S M)) := by
    change Function.Injective (f.toLinearMap.rTensor M)
    exact Module.Flat.rTensor_preserves_injective_linearMap _ hi
  exact e.injective.comp hinj

/-- Intrinsic images of finite-presentation models remain finitely presented
over a Noetherian intermediate coefficient ring. -/
theorem scalarImage_finitePresentation [IsNoetherianRing R]
    [Algebra.FinitePresentation S M] (e : K ⊗[S] M ≃ₐ[K] A) :
    Algebra.FinitePresentation R (scalarImageHom (R := R) e).range := by
  have : Algebra.FiniteType R (scalarImageHom (R := R) e).range :=
    Algebra.FiniteType.of_surjective (scalarImageHom (R := R) e).rangeRestrict
      (scalarImageHom (R := R) e).rangeRestrict_surjective
  exact Algebra.FinitePresentation.of_finiteType.mp this

/-- Smooth initial models retain smoothness in their intrinsic coefficient images. -/
theorem scalarImage_smooth [Algebra.Smooth S M]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Algebra.Smooth R (scalarImageHom (R := R) e).range := by
  exact Algebra.Smooth.of_equiv
    (AlgEquiv.ofInjective (scalarImageHom (R := R) e) (scalarImageHom_injective e hi))

end FrobeniusSplitting
