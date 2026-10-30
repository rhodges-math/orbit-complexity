import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Coefficient extension of polynomial contractions

The extended family is constructed by the tensor universal property. No
polynomial/tensor isomorphism is identified at a concrete coordinate ring.
Its values on pure tensors and its endpoint equations are proved over arbitrary
commutative coefficient rings.
-/

open scoped TensorProduct

noncomputable section

namespace FrobeniusSplitting

universe u

variable {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A]

/-- Extend a polynomial family by evaluating its tensor factors in the same
polynomial ring over the extended coefficient algebra. -/
def polynomialTensorContraction (σ : C →ₐ[R] Polynomial C) :
    A ⊗[R] C →ₐ[A] Polynomial (A ⊗[R] C) :=
  Algebra.TensorProduct.lift (Algebra.ofId A (Polynomial (A ⊗[R] C)))
    ((Polynomial.mapAlgHom
      (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C)).comp σ)
    (fun _ _ => .all _ _)

/-- Extend the scalar-valued origin using the same tensor universal property. -/
def polynomialTensorOrigin (ε : C →ₐ[R] R) : A ⊗[R] C →ₐ[A] A :=
  Algebra.TensorProduct.lift (AlgHom.id A A) ((Algebra.ofId R A).comp ε)
    (fun _ _ => .all _ _)

/-- The extended family has the specified pure-tensor coordinate value. -/
theorem polynomialTensorContraction_tmul (σ : C →ₐ[R] Polynomial C) (a : A) (c : C) :
    polynomialTensorContraction (A := A) σ (a ⊗ₜ[R] c) =
      Polynomial.C (algebraMap A (A ⊗[R] C) a) *
        Polynomial.map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom
          (σ c) := by
  simp only [polynomialTensorContraction, Algebra.TensorProduct.lift_tmul,
    Algebra.ofId_apply, Polynomial.algebraMap_apply, AlgHom.comp_apply,
    Polynomial.coe_mapAlgHom, AlgHom.toRingHom_eq_coe]

/-- The extended origin has the specified pure-tensor value. -/
theorem polynomialTensorOrigin_tmul (ε : C →ₐ[R] R) (a : A) (c : C) :
    polynomialTensorOrigin (A := A) ε (a ⊗ₜ[R] c) = a * algebraMap R A (ε c) := by
  simp only [polynomialTensorOrigin, Algebra.TensorProduct.lift_tmul,
    AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply]

/-- The identity endpoint survives arbitrary coefficient extension. -/
theorem polynomialTensorContraction_one (σ : C →ₐ[R] Polynomial C)
    (hOne : ∀ c : C, (σ c).eval 1 = c) (z : A ⊗[R] C) :
    (polynomialTensorContraction (A := A) σ z).eval 1 = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    rw [polynomialTensorContraction_tmul, Polynomial.eval_mul, Polynomial.eval_C]
    have he : (Polynomial.map
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom
          (σ c)).eval 1 =
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) ((σ c).eval 1) := by
      simpa only [map_one, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        (Polynomial.eval_map_apply
          (f := (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom)
          (p := σ c) (1 : C))
    rw [he, hOne]
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.algebraMap_self_apply]
  | add x y hx hy =>
    simp only [map_add, Polynomial.eval_add, hx, hy]

/-- The scalar zero endpoint survives arbitrary coefficient extension. -/
theorem polynomialTensorContraction_zero (σ : C →ₐ[R] Polynomial C)
    (ε : C →ₐ[R] R)
    (hZero : ∀ c : C, (σ c).eval 0 = algebraMap R C (ε c)) (z : A ⊗[R] C) :
    (polynomialTensorContraction (A := A) σ z).eval 0 =
      algebraMap A (A ⊗[R] C) (polynomialTensorOrigin (A := A) ε z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    rw [polynomialTensorContraction_tmul, Polynomial.eval_mul, Polynomial.eval_C]
    have he : (Polynomial.map
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom
          (σ c)).eval 0 =
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) ((σ c).eval 0) := by
      simpa only [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        (Polynomial.eval_map_apply
          (f := (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom)
          (p := σ c) (0 : C))
    rw [he, hZero, polynomialTensorOrigin_tmul, map_mul]
    congr 1
    exact ((Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).commutes (ε c)).trans
      (IsScalarTower.algebraMap_apply R A (A ⊗[R] C) (ε c))
  | add x y hx hy =>
    simp only [map_add, Polynomial.eval_add, hx, hy]

end FrobeniusSplitting
