import Batteries.Tactic.Lint
import Mathlib.Algebra.Category.Ring.Constructions
import TauCeti.Algebra.TensorProduct.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Relative Models

Coefficient comparisons give scalar comparisons relative to a common chart.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {R K M A : Type*} [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra R A] [Algebra K A] [Algebra M A]
    [IsScalarTower R K A] [IsScalarTower R M A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem pushout_scalar (e : K ⊗[R] M ≃ₐ[K] A)
    (he : ∀ m, e ((1 : K) ⊗ₜ[R] m) = algebraMap M A m) :
    Algebra.IsPushout R K M A := by
  apply Algebra.IsPushout.of_equiv e
  ext m
  exact he m

variable {N B : Type*} [CommRing N] [CommRing B]
    [Algebra R N] [Algebra M N] [IsScalarTower R M N]
    [Algebra R B] [Algebra K B] [Algebra M B] [Algebra N B] [Algebra A B]
    [IsScalarTower R K B] [IsScalarTower R N B]
    [IsScalarTower R A B] [IsScalarTower M N B] [IsScalarTower M A B]
    [IsScalarTower K A B]

/-- Compatible coefficient comparisons give the scalar comparison relative to a common chart. -/
noncomputable def relativeScalarEquiv (eM : K ⊗[R] M ≃ₐ[K] A)
    (eN : K ⊗[R] N ≃ₐ[K] B)
    (hM : ∀ m, eM ((1 : K) ⊗ₜ[R] m) = algebraMap M A m)
    (hN : ∀ n, eN ((1 : K) ⊗ₜ[R] n) = algebraMap N B n) :
    A ⊗[M] N ≃ₐ[A] B := by
  have : IsScalarTower R M B := IsScalarTower.to₁₂₄ R M A B
  have : Algebra.IsPushout R K M A := pushout_scalar eM hM
  have : Algebra.IsPushout R M K A := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout R K N B := pushout_scalar eN hN
  have : Algebra.IsPushout R N K B := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout M N A B :=
    (Algebra.IsPushout.comp_iff R M K (S' := A) (T := N) (T' := B)).mp inferInstance
  have : Algebra.IsPushout M A N B := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv M A N B

/-- The relative scalar comparison sends model elements to their generic images. -/
@[simp] theorem relativeScalarEquiv_tmul (eM : K ⊗[R] M ≃ₐ[K] A)
    (eN : K ⊗[R] N ≃ₐ[K] B)
    (hM : ∀ m, eM ((1 : K) ⊗ₜ[R] m) = algebraMap M A m)
    (hN : ∀ n, eN ((1 : K) ⊗ₜ[R] n) = algebraMap N B n) (n : N) :
    relativeScalarEquiv eM eN hM hN ((1 : A) ⊗ₜ[M] n) = algebraMap N B n := by
  unfold relativeScalarEquiv
  simp only [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- Every element of a ring pushout is a finite sum of products from its two source rings. -/
theorem exists_pushout_product_sum {T U V W : Type*}
    [CommSemiring T] [CommSemiring U] [CommSemiring V] [CommSemiring W]
    [Algebra T U] [Algebra T V] [Algebra T W] [Algebra U W] [Algebra V W]
    [IsScalarTower T U W] [IsScalarTower T V W] [Algebra.IsPushout T U V W] (w : W) :
    ∃ (n : ℕ) (x : Fin n → U) (y : Fin n → V),
      w = ∑ j, algebraMap U W (x j) * algebraMap V W (y j) := by
  let e := Algebra.IsPushout.equiv T U V W
  obtain ⟨n, x, y, h⟩ := TensorProduct.exists_sum_tmul_eq (e.symm w)
  refine ⟨n, x, y, ?_⟩
  calc
    w = e (e.symm w) := (e.apply_symm_apply w).symm
    _ = e (∑ j, x j ⊗ₜ[T] y j) := congrArg e h
    _ = ∑ j, algebraMap U W (x j) * algebraMap V W (y j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact Algebra.IsPushout.equiv_tmul T U V W (x j) (y j)

end FrobeniusSplitting
