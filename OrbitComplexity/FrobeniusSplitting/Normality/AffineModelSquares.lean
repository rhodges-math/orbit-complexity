import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.AffineModelDiagrams

/-!
# Commutative squares of affine scalar models
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Scalar-compatible algebra maps give a commutative square of spectrum comparisons. -/
theorem affineModel_map_square {R K A₀ B₀ A B : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing B]
    [Algebra R A₀] [Algebra R B₀] [Algebra K A] [Algebra K B]
    (eA : K ⊗[R] A₀ ≃ₐ[K] A) (eB : K ⊗[R] B₀ ≃ₐ[K] B)
    (φ : A →ₐ[K] B) (φ₀ : A₀ →ₐ[R] B₀)
    (hφ : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K φ₀) =
      φ.comp eA.toAlgHom) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (eA.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) =
      Spec.map (CommRingCat.ofHom
          (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom φ₀.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro x
  have h := AlgHom.congr_fun hφ ((1 : K) ⊗ₜ[R] x)
  change eB ((1 : K) ⊗ₜ[R] φ₀ x) = φ (eA ((1 : K) ⊗ₜ[R] x)) at h
  exact h.symm

end FrobeniusSplitting
