import Batteries.Tactic.Lint
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization Comparison

Scalar-extension comparisons identify principal localization algebras.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S K M N A B : Type*}
    [CommRing S] [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra S K] [Algebra S M] [Algebra S N] [Algebra M N] [IsScalarTower S M N]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

/-- A scalar-extension comparison transports a principal localization to its generic algebra. -/
theorem localization_of_scalar_comparison
    (e : K ⊗[S] M ≃ₐ[K] A) (d : K ⊗[S] N ≃ₐ[K] B)
    (g : M) [IsLocalization.Away g N]
    (hcomm : ∀ k m, d (k ⊗ₜ[S] algebraMap M N m) =
      algebraMap A B (e (k ⊗ₜ[S] m))) :
    IsLocalization.Away (e ((1 : K) ⊗ₜ[S] g)) B := by
  let T := K ⊗[S] M
  let F := K ⊗[S] N
  let ψ : T →ₐ[K] F :=
    Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom S M N)
  let : Algebra T F := ψ.toAlgebra
  have : IsScalarTower K T F :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (ψ.commutes k).symm
  let u : T →ₐ[K] B := (IsScalarTower.toAlgHom K A B).comp e.toAlgHom
  let : Algebra T B := u.toAlgebra
  have : IsScalarTower K T B :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (u.commutes k).symm
  have hloc : IsLocalization.Away ((1 : K) ⊗ₜ[S] g) F := by
    have hl := IsLocalization.tensorProduct_tensorProduct_right S K
      (Submonoid.powers g) N (by ext m; rfl)
    simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using hl
  have hsquare : d.toAlgHom.comp ψ = u := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul k m => exact hcomm k m
    | add x y hx hy => simp only [map_add, hx, hy]
  let dT : F ≃ₐ[T] B :=
    { d.toRingEquiv with
      commutes' := fun x ↦ AlgHom.congr_fun hsquare x }
  have : IsLocalization.Away ((1 : K) ⊗ₜ[S] g) B :=
    IsLocalization.isLocalization_of_algEquiv _ dT
  have hM : (Submonoid.powers (e ((1 : K) ⊗ₜ[S] g))).map e.symm.toRingEquiv =
      Submonoid.powers ((1 : K) ⊗ₜ[S] g) := by
    rw [Submonoid.map_powers]
    change Submonoid.powers (e.symm (e ((1 : K) ⊗ₜ[S] g))) = _
    rw [e.symm_apply_apply]
  exact IsLocalization.of_ringEquiv_left e.symm.toRingEquiv hM fun a ↦ by
    change algebraMap A B a = algebraMap A B (e (e.symm a))
    rw [e.apply_symm_apply]

end FrobeniusSplitting
