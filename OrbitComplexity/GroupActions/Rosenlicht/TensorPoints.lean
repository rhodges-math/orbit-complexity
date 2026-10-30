import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Point evaluations of scalar-extended equations

Points of a reduced affine algebra over an algebraically closed field detect
equations after arbitrary scalar extension. Consequently the kernel of a map into
that scalar extension is the intersection of its pointwise specialized kernels.

## Main definitions

* `tensorPointEval`: evaluation of the first tensor factor at a base-valued point.

## Main results

* `tensorPointEval_jointlyInjective`: all base-valued evaluations detect tensor equality.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w x

section Evaluation

variable {K : Type u} [CommRing K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {B : Type w} [CommRing B] [Algebra K B]

/-- Evaluate the first factor of a tensor product at a base-valued point. -/
def tensorPointEval (g : A →ₐ[K] K) : A ⊗[K] B →ₐ[K] B :=
  (Algebra.TensorProduct.lid K B).toAlgHom.comp
    (Algebra.TensorProduct.map g (AlgHom.id K B))

/-- Evaluation of a pure tensor is scalar multiplication by the value of its first factor. -/
theorem tensorPointEval_tmul (g : A →ₐ[K] K) (a : A) (b : B) :
    tensorPointEval g (a ⊗ₜ[K] b) = g a • b := by
  simp [tensorPointEval]

end Evaluation

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable [Algebra.FiniteType K A] [IsReduced A]
variable {B : Type w} [CommRing B] [Algebra K B]

/-- Base-valued points jointly detect equality after scalar extension of a reduced
finite-type algebra over an algebraically closed field. -/
theorem tensorPointEval_jointlyInjective {s t : A ⊗[K] B}
    (h : ∀ g : A →ₐ[K] K, tensorPointEval g s = tensorPointEval g t) : s = t := by
  apply TauCeti.tensor_eq_of_forall_map_algHom_eq (K := K)
  intro g
  apply (TensorProduct.lid K B).injective
  exact h g

end

end GroupActions
