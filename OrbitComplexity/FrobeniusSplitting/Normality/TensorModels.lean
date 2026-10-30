import Batteries.Tactic.Lint
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# TensorModels

Tensor and localization comparisons for coefficient models.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M A B : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra R M] [Algebra S M] [IsScalarTower S R M]
    [Algebra K A] [Algebra S A] [IsScalarTower S K A] [Algebra S B]

/-- Extending a coefficient model commutes with tensoring by a fixed fibre algebra. -/
noncomputable def tensorModelEquiv (e : K ⊗[R] M ≃ₐ[K] A) :
    K ⊗[R] (M ⊗[S] B) ≃ₐ[K] A ⊗[S] B :=
  (Algebra.TensorProduct.assoc S R K K M B).symm.trans
    (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := S) (A₁ := B)))

/-- The product comparison sends a pure tensor to the corresponding fibre tensor. -/
theorem tensorModelEquiv_tmul (e : K ⊗[R] M ≃ₐ[K] A) (k : K) (m : M) (b : B) :
    tensorModelEquiv e (k ⊗ₜ[R] (m ⊗ₜ[S] b)) = e (k ⊗ₜ[R] m) ⊗ₜ[S] b := rfl

end FrobeniusSplitting
