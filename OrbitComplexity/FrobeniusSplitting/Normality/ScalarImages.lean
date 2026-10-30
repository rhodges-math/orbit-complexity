import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelComparison
import OrbitComplexity.FrobeniusSplitting.Normality.ImageLocalizationMap
import OrbitComplexity.FrobeniusSplitting.Normality.LocalizationComparison
import OrbitComplexity.FrobeniusSplitting.Normality.ModelImages
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Scalar Images

Intrinsic scalar-extension images preserve principal localization algebras.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

variable {S R K M N ι σ ι' σ' : Type*} {A B : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing N]
    [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra S N] [Algebra K A] [Algebra K B]
    [Algebra R A] [Algebra R B] [IsScalarTower R K A] [IsScalarTower R K B]

/-- Evaluation in a scalar-extension comparison over an intermediate coefficient ring. -/
def scalarImageHom (e : K ⊗[S] M ≃ₐ[K] A) : R ⊗[S] M →ₐ[R] A :=
  (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.map (Algebra.ofId R K) (AlgHom.id S M))

/-- The image of a chosen presentation agrees with intrinsic scalar-extension evaluation. -/
theorem modelImage_eq_scalarImage (Q : Algebra.Presentation S M ι σ)
    (e : K ⊗[S] M ≃ₐ[K] A)
    [((Q.baseChange K).ofAlgEquiv e).HasCoeffs R]
    (hi : Function.Injective (algebraMap R K)) :
    (tensorImageHom (((Q.baseChange K).ofAlgEquiv e).tensorModelOfHasCoeffsEquiv R)).range =
      (scalarImageHom (R := R) e).range := by
  let E := baseChangeModelEquivOf Q e hi
  have h : tensorImageHom
      (((Q.baseChange K).ofAlgEquiv e).tensorModelOfHasCoeffsEquiv R) =
      (scalarImageHom (R := R) e).comp E.toAlgHom := by
    apply AlgHom.ext
    intro m
    exact baseChangeModelEquiv_naturality Q e hi m
  rw [h, AlgHom.range_comp]
  rw [(AlgHom.range_eq_top E.toAlgHom).mpr E.surjective, Algebra.map_top]

/-- Scalar-extension images preserve the localization algebra and its denominator. -/
theorem scalarImage_localization
    [Algebra M N] [IsScalarTower S M N]
    [Algebra A B] [IsScalarTower K A B] [IsScalarTower R A B]
    (e : K ⊗[S] M ≃ₐ[K] A) (d : K ⊗[S] N ≃ₐ[K] B)
    (g : M) [IsLocalization.Away g N]
    (hcomm : ∀ k m, d (k ⊗ₜ[S] algebraMap M N m) =
      algebraMap A B (e (k ⊗ₜ[S] m))) :
    let q := scalarImageHom (R := R) e
    let r := scalarImageHom (R := R) d
    let z : R ⊗[S] M := (1 : R) ⊗ₜ[S] g
    ∃ map : q.range →ₐ[R] r.range,
      (∀ a, (map a : B) = algebraMap A B (a : A)) ∧
      letI : Algebra q.range r.range := map.toAlgebra
      IsLocalization.Away (⟨q z, ⟨z, rfl⟩⟩ : q.range) r.range := by
  have : IsLocalization.Away (e ((1 : K) ⊗ₜ[S] g)) B :=
    localization_of_scalar_comparison e d g hcomm
  let q := scalarImageHom (R := R) e
  let r := scalarImageHom (R := R) d
  let z : R ⊗[S] M := (1 : R) ⊗ₜ[S] g
  let ψ : R ⊗[S] M →ₐ[R] R ⊗[S] N :=
    Algebra.TensorProduct.map (AlgHom.id R R) (IsScalarTower.toAlgHom S M N)
  let : Algebra (R ⊗[S] M) (R ⊗[S] N) := ψ.toAlgebra
  have : IsScalarTower R (R ⊗[S] M) (R ⊗[S] N) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  have hloc : IsLocalization.Away z (R ⊗[S] N) := by
    have hl := IsLocalization.tensorProduct_tensorProduct_right S R
      (Submonoid.powers g) N (by ext m; rfl)
    simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using hl
  have hz : q z = e ((1 : K) ⊗ₜ[S] g) := by
    simp [q, z, scalarImageHom, Algebra.TensorProduct.map_tmul]
  have : IsLocalization.Away (q z) B := by rw [hz]; infer_instance
  have hsquare : r.comp (IsScalarTower.toAlgHom R (R ⊗[S] M) (R ⊗[S] N)) =
      (IsScalarTower.toAlgHom R A B).comp q := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      change d (algebraMap R K a ⊗ₜ[S] algebraMap M N m) =
        algebraMap A B (e (algebraMap R K a ⊗ₜ[S] m))
      exact hcomm (algebraMap R K a) m
    | add x y hx hy => simp only [map_add, hx, hy]
  exact localization_image_of_commutes q z r hsquare

end FrobeniusSplitting
