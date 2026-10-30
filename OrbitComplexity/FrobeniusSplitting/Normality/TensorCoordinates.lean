import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Polynomial and Laurent coordinates under tensor scalar extension -/

noncomputable section

universe u v w

namespace FrobeniusSplitting

section Part1

open scoped TensorProduct

variable (S R : Type*) [CommSemiring S] [CommSemiring R] [Algebra S R]

/-- Scalar extension of a univariate polynomial algebra preserves its coordinate. -/
noncomputable def polynomialTensorEquiv : R ⊗[S] Polynomial S ≃ₐ[R] Polynomial R :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (Polynomial.toFinsuppIsoAlg S)).trans
      ((AddMonoidAlgebra.scalarTensorEquiv S R).trans (Polynomial.toFinsuppIsoAlg R).symm)

/-- The coefficient of a scalar-extended pure tensor is the extended coefficient. -/
private theorem polynomialTensorEquiv_coeff (a : R) (p : Polynomial S) (n : ℕ) :
    (polynomialTensorEquiv S R (a ⊗ₜ[S] p)).coeff n = a * algebraMap S R (p.coeff n) := by
  change ((AddMonoidAlgebra.scalarTensorEquiv S R)
    (a ⊗ₜ[S] (Polynomial.toFinsuppIsoAlg S p))).coeff n = _
  rw [AddMonoidAlgebra.scalarTensorEquiv_tmul]
  simp only [AddMonoidAlgebra.coeff_smul]
  rfl

/-- A pure tensor maps to the coefficientwise polynomial extension with its scalar factor. -/
theorem polynomialTensorEquiv_tmul (a : R) (p : Polynomial S) :
    polynomialTensorEquiv S R (a ⊗ₜ[S] p) =
      Polynomial.C a * p.map (algebraMap S R) := by
  ext n
  rw [polynomialTensorEquiv_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map]

/-- Scalar extension of the Laurent coordinate is computed coefficientwise. -/
private theorem laurentTensor_coeff (a : R) (p : LaurentPolynomial S) (n : ℤ) :
    ((AddMonoidAlgebra.scalarTensorEquiv S R) (a ⊗ₜ[S] p)).coeff n =
      a * algebraMap S R (p.coeff n) := by
  rw [AddMonoidAlgebra.scalarTensorEquiv_tmul]
  rfl

/-- Scalar extension respects the polynomial inclusion in Laurent polynomials. -/
theorem polynomialTensor_toLaurent (a : R) (p : Polynomial S) :
    (AddMonoidAlgebra.scalarTensorEquiv S R) (a ⊗ₜ[S] p.toLaurent) =
      (polynomialTensorEquiv S R (a ⊗ₜ[S] p)).toLaurent := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hp hq
  | monomial n s =>
    ext k
    rw [laurentTensor_coeff, polynomialTensorEquiv_tmul]
    simp [Polynomial.C_mul_monomial, ← LaurentPolynomial.single_eq_C_mul_T]
    rw [← map_mul, ← LaurentPolynomial.single_eq_C_mul_T]
    change a * algebraMap S R (Finsupp.single (n : ℤ) s k) =
      Finsupp.single (n : ℤ) (a * algebraMap S R s) k
    by_cases h : (n : ℤ) = k <;> simp [h]

/-- Scalar extension respects reciprocal Laurent coordinates. -/
theorem laurentTensor_invert (a : R) (p : LaurentPolynomial S) :
    (AddMonoidAlgebra.scalarTensorEquiv S R) (a ⊗ₜ[S] LaurentPolynomial.invert p) =
      LaurentPolynomial.invert ((AddMonoidAlgebra.scalarTensorEquiv S R) (a ⊗ₜ[S] p)) := by
  ext n
  simp only [laurentTensor_coeff, LaurentPolynomial.invert_apply]

end Part1

section Part2

open scoped TensorProduct

/-- A tensor-coordinate comparison carries specified coordinates to their scalar extensions. -/
theorem tensorCoordinate_apply {S R A B C D : Type*}
    [CommSemiring S] [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [CommSemiring C] [CommSemiring D] [Algebra S R] [Algebra S A] [Algebra S B]
    [Algebra R C] [Algebra R D]
    (e : A ≃ₐ[S] B) (d : R ⊗[S] A ≃ₐ[R] C) (g : C ≃ₐ[R] D) (r : R) (a : A) :
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e.symm).trans
      (d.trans g)) (r ⊗ₜ[S] e a) = g (d (r ⊗ₜ[S] a)) := by
  change g (d (r ⊗ₜ[S] e.symm (e a))) = _
  rw [AlgEquiv.symm_apply_apply]

end Part2

section Part3

open scoped TensorProduct

/-- Pure-tensor comparison equations determine naturality of a scalar-extended algebra map. -/
theorem tensor_map_naturality {S R A B P Q : Type*}
    [CommSemiring S] [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [CommSemiring P] [CommSemiring Q] [Algebra S R] [Algebra S A] [Algebra S B]
    [Algebra R P] [Algebra R Q]
    (e : R ⊗[S] A ≃ₐ[R] P) (d : R ⊗[S] B ≃ₐ[R] Q)
    (f : A →ₐ[S] B) (g : P →ₐ[R] Q)
    (h : ∀ r a, d (r ⊗ₜ[S] f a) = g (e (r ⊗ₜ[S] a))) :
    d.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id R R) f) =
      g.comp e.toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r a => exact h r a
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Part3

end FrobeniusSplitting
