import Batteries.Tactic.Lint
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Scalar Localization

Localization comparisons extend scalar-extension comparisons on model elements.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S K M A B : Type*} [CommRing S] [CommRing K] [CommRing M]
    [CommRing A] [CommRing B] [Algebra S K] [Algebra S M]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (e : K ⊗[S] M ≃ₐ[K] A) (g : M) (f : A) [IsLocalization.Away f B]
    (hg : e ((1 : K) ⊗ₜ[S] g) = f)

/-- Localization of a scalar-extension model recovers localization at the corresponding element. -/
noncomputable def localizationScalarEquiv : K ⊗[S] Localization.Away g ≃ₐ[K] B := by
  let u : K ⊗[S] M →ₐ[K] B := (IsScalarTower.toAlgHom K A B).comp e.toAlgHom
  let : Algebra (K ⊗[S] M) B := u.toAlgebra
  have : IsScalarTower K (K ⊗[S] M) B :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (u.commutes k).symm
  have hM : (Submonoid.powers ((1 : K) ⊗ₜ[S] g)).map e.toRingEquiv =
      Submonoid.powers f := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers hg
  have : IsLocalization.Away ((1 : K) ⊗ₜ[S] g) B :=
    IsLocalization.of_ringEquiv_left e.toRingEquiv hM (fun _ ↦ rfl)
  exact (IsLocalization.Away.tensorProductEquivTMulRight S K g
    (Localization.Away g)).trans
      ((IsLocalization.algEquiv (Submonoid.powers ((1 : K) ⊗ₜ[S] g))
        (Localization.Away ((1 : K) ⊗ₜ[S] g)) B).restrictScalars K)

/-- The localization comparison extends the original comparison on model elements. -/
theorem localizationScalarEquiv_tmul (k : K) (m : M) :
    localizationScalarEquiv e g f hg (k ⊗ₜ[S] algebraMap M (Localization.Away g) m) =
      algebraMap A B (e (k ⊗ₜ[S] m)) := by
  let u : K ⊗[S] M →ₐ[K] B := (IsScalarTower.toAlgHom K A B).comp e.toAlgHom
  let : Algebra (K ⊗[S] M) B := u.toAlgebra
  have : IsScalarTower K (K ⊗[S] M) B :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (u.commutes k).symm
  unfold localizationScalarEquiv
  dsimp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul, AlgEquiv.commutes]
  rfl

end FrobeniusSplitting
