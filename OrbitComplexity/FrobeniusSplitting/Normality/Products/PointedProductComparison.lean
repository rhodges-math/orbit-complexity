import Mathlib.RingTheory.TensorProduct.Maps

/-! # Product comparisons and retained point retractions

Scalar extension identifies the tensor product of two coefficient
models with the product. The point retraction is compatible with that
comparison when the point itself is retained.
-/

open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section

variable {R K A B C D : Type*}
  [CommRing R] [CommRing K] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R K] [Algebra R A] [Algebra R B] [Algebra K C] [Algebra K D]

/-- The generic comparison of two tensor-factor models. -/
def productModelEquiv (eA : K ⊗[R] A ≃ₐ[K] C) (eB : K ⊗[R] B ≃ₐ[K] D) :
    K ⊗[R] (A ⊗[R] B) ≃ₐ[K] C ⊗[K] D :=
  (Algebra.TensorProduct.assoc R R K K A B).symm.trans
    ((Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] A) B).symm.trans
      (Algebra.TensorProduct.congr eA eB))

/-- The product comparison evaluates an pure tensor in both factors. -/
theorem productModelEquiv_tmul (eA : K ⊗[R] A ≃ₐ[K] C)
    (eB : K ⊗[R] B ≃ₐ[K] D) (k : K) (a : A) (b : B) :
    productModelEquiv eA eB (k ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      eA (k ⊗ₜ[R] a) ⊗ₜ[K] eB ((1 : K) ⊗ₜ[R] b) := rfl

/-- A point on the second factor defines the product retraction. -/
def pointedProductRetraction (eps : B →ₐ[R] R) : A ⊗[R] B →ₐ[R] A :=
  Algebra.TensorProduct.lift (AlgHom.id R A) ((Algebra.ofId R A).comp eps)
    (fun _ _ => Commute.all _ _)

/-- The product retraction evaluates a pure tensor through the point. -/
theorem pointedProductRetraction_tmul (eps : B →ₐ[R] R) (a : A) (b : B) :
    pointedProductRetraction (A := A) eps (a ⊗ₜ[R] b) =
      a * algebraMap R A (eps b) := rfl

/-- The product retraction splits the first-factor inclusion. -/
theorem pointedProductRetraction_section (eps : B →ₐ[R] R) :
    (pointedProductRetraction (A := A) eps).comp
      ((Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[R] B).restrictScalars R) =
      AlgHom.id R A := by
  ext a
  change a * algebraMap R A (eps 1) = a
  simp only [map_one, mul_one]

/-- The retained point makes the product comparison commute with the
retraction, as an equality of algebra maps. -/
theorem productModelEquiv_retraction (eA : K ⊗[R] A ≃ₐ[K] C)
    (eB : K ⊗[R] B ≃ₐ[K] D) (eps : D →ₐ[K] K) (eps0 : B →ₐ[R] R)
    (heps : ∀ (k : K) (b : B),
      eps (eB (k ⊗ₜ[R] b)) = k * algebraMap R K (eps0 b)) :
    eA.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K K)
        (pointedProductRetraction (A := A) eps0)) =
      (pointedProductRetraction (A := C) eps).comp (productModelEquiv eA eB).toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul k z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
      | tmul a b =>
          change eA (k ⊗ₜ[R] (a * algebraMap R A (eps0 b))) =
            pointedProductRetraction (A := C) eps
              (productModelEquiv eA eB (k ⊗ₜ[R] (a ⊗ₜ[R] b)))
          rw [productModelEquiv_tmul, pointedProductRetraction_tmul, heps, one_mul]
          rw [mul_comm a, ← Algebra.smul_def, TensorProduct.tmul_smul]
          rw [← IsScalarTower.algebraMap_smul K (eps0 b) (k ⊗ₜ[R] a),
            map_smul, Algebra.smul_def, mul_comm]

end
end FrobeniusSplitting
