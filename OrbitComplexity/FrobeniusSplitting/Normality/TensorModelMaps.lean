import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.TensorModels
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoefficients

/-!
# TensorModelMaps

Arithmetic coefficient models and compatible chart comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K A B : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra K A] [Algebra R A] [Algebra S A]
    [IsScalarTower S K A] [IsScalarTower S R A]
    [Algebra S B] (M : Subalgebra R A)
    (e : K ⊗[R] M ≃ₐ[K] A) (he : ∀ m : M, e ((1 : K) ⊗ₜ[R] m) = m.val)

include he

/-- Evaluation of a product coefficient model is its tensor inclusion into the generic algebra. -/
theorem tensorModelEquiv_evalOne (z : M ⊗[S] B) :
    tensorModelEquiv (B := B) e ((1 : K) ⊗ₜ[R] z) =
      Algebra.TensorProduct.map (M.val.restrictScalars S) (AlgHom.id S B) z := by
  induction z using TensorProduct.inductionOn with
  | tmul m b =>
    rw [tensorModelEquiv_tmul, he]
    rfl
  | add z w hz hw =>
    simp only [TensorProduct.tmul_add, map_add, hz, hw]

end FrobeniusSplitting
