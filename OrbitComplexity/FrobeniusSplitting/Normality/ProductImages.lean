import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.TensorModels
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoefficients
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages

/-!
# ProductImages

Tensor and localization comparisons for coefficient models.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K A B F : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing A] [CommRing B] [CommRing F]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S B] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- The intrinsic coefficient image of a fixed product is the range of the tensor
inclusion from the intrinsic coefficient image of its base. -/
theorem scalarImage_product_range (e : K ⊗[S] B ≃ₐ[K] A) :
    (scalarImageHom (R := R) (tensorModelEquiv (S := ℤ) e
      (B := F))).range =
      (Algebra.TensorProduct.map (scalarImageHom (R := R) e).range.val
        (AlgHom.id ℤ F)).range := by
  let q : R ⊗[S] B →ₐ[R] A := scalarImageHom (R := R) e
  let p := scalarImageHom (R := R) (tensorModelEquiv (S := ℤ) e (B := F))
  let i : (q.range ⊗[ℤ] F) →ₐ[R] (A ⊗[ℤ] F) :=
    Algebra.TensorProduct.map q.range.val (AlgHom.id ℤ F)
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul r z =>
      induction z using TensorProduct.inductionOn with
      | tmul b f =>
        exact ⟨(⟨q (r ⊗ₜ[S] b), ⟨r ⊗ₜ[S] b, rfl⟩⟩ : q.range) ⊗ₜ[ℤ] f, rfl⟩
      | add z w hz hw =>
        simpa only [TensorProduct.tmul_add, map_add] using i.range.add_mem hz hw
    | add z w hz hw =>
      simpa only [map_add] using i.range.add_mem hz hw
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul m f =>
      obtain ⟨x, hx⟩ := m.property
      have hmem (x : R ⊗[S] B) : q x ⊗ₜ[ℤ] f ∈ p.range := by
        induction x using TensorProduct.inductionOn with
        | tmul r b => exact ⟨r ⊗ₜ[S] (b ⊗ₜ[ℤ] f), rfl⟩
        | add x y hx hy =>
          simpa only [map_add, TensorProduct.add_tmul] using p.range.add_mem hx hy
      change m.val ⊗ₜ[ℤ] f ∈ p.range
      rw [← hx]
      exact hmem x
    | add x y hx hy =>
      simpa only [map_add] using p.range.add_mem hx hy

/-- Flat fixed-fibre factors identify a product coefficient algebra with
the intrinsic image of its scalar-extension model. -/
noncomputable def productImageEquiv [Module.Flat ℤ F] (e : K ⊗[S] B ≃ₐ[K] A) :
    (scalarImageHom (R := R) e).range ⊗[ℤ] F ≃ₐ[R]
      (scalarImageHom (R := R) (tensorModelEquiv (S := ℤ) e (B := F))).range :=
  (AlgEquiv.ofInjective
    (Algebra.TensorProduct.map (scalarImageHom (R := R) e).range.val (AlgHom.id ℤ F))
      (tensor_subalgebra_injective
        ((scalarImageHom (R := R) e).range.restrictScalars ℤ))).trans
    (Subalgebra.equivOfEq _ _ (scalarImage_product_range e).symm)

/-- The product image comparison evaluates by the tensor of the base inclusion. -/
theorem productImageEquiv_apply [Module.Flat ℤ F] (e : K ⊗[S] B ≃ₐ[K] A)
    (z : (scalarImageHom (R := R) e).range ⊗[ℤ] F) :
    (productImageEquiv e z : A ⊗[ℤ] F) =
      Algebra.TensorProduct.map (scalarImageHom (R := R) e).range.val
        (AlgHom.id ℤ F) z := rfl

end FrobeniusSplitting
