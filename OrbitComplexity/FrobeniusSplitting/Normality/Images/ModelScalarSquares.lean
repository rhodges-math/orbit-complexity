import OrbitComplexity.FrobeniusSplitting.Normality.Images.EndpointKernelTransport
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Model comparison squares under successive scalar extensions -/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

open private cancel_map_square
  from OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement
open private tensor_equiv_square
  from OrbitComplexity.FrobeniusSplitting.Normality.Images.EndpointKernelTransport

private theorem rebased_comparison_square {S R K A B A' B' : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S A] [Algebra S B] [Algebra K A'] [Algebra K B']
    (eA : K ⊗[S] A ≃ₐ[K] A') (eB : K ⊗[S] B ≃ₐ[K] B')
    (g : A →ₐ[S] B) (g' : A' →ₐ[K] B')
    (h : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K g) =
      g'.comp eA.toAlgHom) :
    ((Algebra.TensorProduct.cancelBaseChange S R K K B).trans eB).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K
          (Algebra.TensorProduct.lTensor (S := R) R g)) =
      g'.comp
        ((Algebra.TensorProduct.cancelBaseChange S R K K A).trans eA).toAlgHom := by
  apply AlgHom.ext
  intro z
  change eB (Algebra.TensorProduct.cancelBaseChange S R K K B
      (Algebra.TensorProduct.lTensor (S := K) K
        (Algebra.TensorProduct.lTensor (S := R) R g) z)) =
    g' (eA (Algebra.TensorProduct.cancelBaseChange S R K K A z))
  rw [cancel_map_square]
  exact AlgHom.congr_fun h (Algebra.TensorProduct.cancelBaseChange S R K K A z)

private theorem cancelled_model_square {S R T A B A' B' : Type u}
    [CommRing S] [CommRing R] [CommRing T]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B] [Algebra R A'] [Algebra R B']
    (g : A →ₐ[S] B) (g' : A' →ₐ[R] B')
    (eA : T ⊗[R] (R ⊗[S] A) ≃ₐ[T] T ⊗[R] A')
    (eB : T ⊗[R] (R ⊗[S] B) ≃ₐ[T] T ⊗[R] B')
    (h : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R g)) =
      (Algebra.TensorProduct.lTensor (S := T) T g').comp eA.toAlgHom) :
    ((Algebra.TensorProduct.cancelBaseChange S R T T B).symm.trans eB).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := T) T g) =
      (Algebra.TensorProduct.lTensor (S := T) T g').comp
        ((Algebra.TensorProduct.cancelBaseChange S R T T A).symm.trans eA).toAlgHom := by
  apply AlgHom.ext
  intro z
  let cA := Algebra.TensorProduct.cancelBaseChange S R T T A
  let cB := Algebra.TensorProduct.cancelBaseChange S R T T B
  have hz : Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R g) (cA.symm z) =
      cB.symm (Algebra.TensorProduct.lTensor (S := T) T g z) := by
    apply cB.injective
    rw [cancel_map_square, cA.apply_symm_apply, cB.apply_symm_apply]
  change eB (cB.symm (Algebra.TensorProduct.lTensor (S := T) T g z)) =
    Algebra.TensorProduct.lTensor (S := T) T g' (eA (cA.symm z))
  rw [← hz]
  exact AlgHom.congr_fun h (cA.symm z)

private def extendModelEquiv {S T R A B : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra S A] [Algebra S B]
    (e : T ⊗[S] A ≃ₐ[T] T ⊗[S] B) : R ⊗[S] A ≃ₐ[R] R ⊗[S] B :=
  (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans
      (Algebra.TensorProduct.cancelBaseChange S T R R B))

private theorem extended_model_square {S T R A B A' B' : Type u}
    [CommRing S] [CommRing T] [CommRing R]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra S A] [Algebra S B] [Algebra S A'] [Algebra S B']
    (g : A →ₐ[S] B) (g' : A' →ₐ[S] B')
    (eA : T ⊗[S] A ≃ₐ[T] T ⊗[S] A')
    (eB : T ⊗[S] B ≃ₐ[T] T ⊗[S] B')
    (h : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := T) T g) =
      (Algebra.TensorProduct.lTensor (S := T) T g').comp eA.toAlgHom) :
    (extendModelEquiv (R := R) eB).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := R) R g) =
      (Algebra.TensorProduct.lTensor (S := R) R g').comp
        (extendModelEquiv (R := R) eA).toAlgHom := by
  apply AlgHom.ext
  intro z
  let cA := Algebra.TensorProduct.cancelBaseChange S T R R A
  let cB := Algebra.TensorProduct.cancelBaseChange S T R R B
  let dA := Algebra.TensorProduct.cancelBaseChange S T R R A'
  let dB := Algebra.TensorProduct.cancelBaseChange S T R R B'
  let tA := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eA
  let tB := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eB
  have hz : Algebra.TensorProduct.lTensor (S := R) R
        (Algebra.TensorProduct.lTensor (S := T) T g) (cA.symm z) =
      cB.symm (Algebra.TensorProduct.lTensor (S := R) R g z) := by
    apply cB.injective
    rw [cancel_map_square, cA.apply_symm_apply, cB.apply_symm_apply]
  have hT := AlgHom.congr_fun
    (tensor_equiv_square (F := R) eA eB
      (Algebra.TensorProduct.lTensor (S := T) T g)
      (Algebra.TensorProduct.lTensor (S := T) T g') h) (cA.symm z)
  change dB (tB (cB.symm (Algebra.TensorProduct.lTensor (S := R) R g z))) =
    Algebra.TensorProduct.lTensor (S := R) R g' (dA (tA (cA.symm z)))
  rw [← hz]
  exact (congrArg dB hT).trans (cancel_map_square g' (tA (cA.symm z)))

end FrobeniusSplitting
