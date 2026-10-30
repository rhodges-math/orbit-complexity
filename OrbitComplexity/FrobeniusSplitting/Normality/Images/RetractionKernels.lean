import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Maps
import Batteries.Tactic.Lint

/-! # Kernels after tensoring a split injection

A linear retraction makes an algebra map injective after every extension of
scalars. Composing with that map therefore leaves the kernel unchanged.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

private theorem tensor_injective_of_retraction
    {R B P : Type*} [CommRing R] [CommRing B] [CommRing P]
    [Algebra R B] [Algebra R P]
    (g : B →ₐ[R] P) (r : P →ₗ[R] B)
    (hr : r.comp g.toLinearMap = LinearMap.id)
    (L : Type*) [CommRing L] [Algebra R L] :
    Function.Injective (Algebra.TensorProduct.lTensor (S := L) L g) := by
  have hrg (b : B) : r (g b) = b :=
    congrArg (fun t : B →ₗ[R] B => t b) hr
  have hleft : Function.LeftInverse (r.lTensor L)
      (Algebra.TensorProduct.lTensor (S := L) L g) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l b =>
        change l ⊗ₜ[R] r (g b) = l ⊗ₜ[R] b
        rw [hrg]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
  exact hleft.injective

/-- A retracted algebra map does not change kernels under composition after
any extension of scalars. -/
theorem tensor_kernel_comp_of_retraction
    {R A B P : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R P]
    (b : A →ₐ[R] B) (g : B →ₐ[R] P) (r : P →ₗ[R] B)
    (hr : r.comp g.toLinearMap = LinearMap.id)
    (L : Type*) [CommRing L] [Algebra R L] :
    RingHom.ker
        (Algebra.TensorProduct.lTensor (S := L) L (g.comp b)).toRingHom =
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L b).toRingHom := by
  have hcomp : Algebra.TensorProduct.lTensor (S := L) L (g.comp b) =
      (Algebra.TensorProduct.lTensor (S := L) L g).comp
        (Algebra.TensorProduct.lTensor (S := L) L b) := by
    ext a
    rfl
  rw [hcomp]
  exact RingHom.ker_comp_of_injective
    (Algebra.TensorProduct.lTensor (S := L) L b).toRingHom
    (tensor_injective_of_retraction g r hr L)

end FrobeniusSplitting
