import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.KrullDimension.Integral

/-! # Dimensions after scalar extension of integral maps

An injective integral ring map induces a surjective morphism on spectra. Surjectivity
persists under scalar extension, so the going-up and incomparability comparisons give
equality of the scalar-extended Krull dimensions.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

universe u

/-- Scalar extension of an injective integral map preserves the base ring's Krull dimension. -/
theorem ringKrullDim_tensor_of_integral (R A C : Type u) [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] [Algebra.IsIntegral R A]
    [FaithfulSMul R A] : ringKrullDim (C ⊗[R] A) = ringKrullDim C := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨Algebra.IsIntegral.comap_surjective R A⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] A)))) := by
    rw [← pullbackSpecIso_inv_fst' R C A]
    infer_instance
  have hs : Function.Surjective (PrimeSpectrum.comap (algebraMap C (C ⊗[R] A))) :=
    (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] A)))).surjective
  exact TauCeti.ringKrullDim_le_of_isIntegral.antisymm
    (TauCeti.ringKrullDim_le_of_hasGoingUp_of_surjective hs)

/-- Every field fibre of an injective integral polynomial normalization has the
dimension given by its number of parameters. -/
theorem ringKrullDim_fibre_of_normalization (R A k : Type u) [CommRing R]
    [CommRing A] [Field k] [Algebra R A] [Algebra R k] (n : ℕ)
    (f : MvPolynomial (Fin n) R →ₐ[R] A) (hinj : Function.Injective f)
    (hint : f.IsIntegral) : ringKrullDim (k ⊗[R] A) = n := by
  let P := MvPolynomial (Fin n) R
  let : Algebra P A := f.toRingHom.toAlgebra
  have : IsScalarTower R P A := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let e : ((P ⊗[R] k) ⊗[P] A) ≃+* (k ⊗[R] A) :=
    (Algebra.TensorProduct.comm P (P ⊗[R] k) A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R P P A k).toRingEquiv.trans
        (Algebra.TensorProduct.comm R A k).toRingEquiv)
  let e' : (P ⊗[R] k) ≃+* MvPolynomial (Fin n) k :=
    (Algebra.TensorProduct.comm R P k).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv R k).toRingEquiv
  calc
    ringKrullDim (k ⊗[R] A) = ringKrullDim ((P ⊗[R] k) ⊗[P] A) :=
      (ringKrullDim_eq_of_ringEquiv e).symm
    _ = ringKrullDim (P ⊗[R] k) := ringKrullDim_tensor_of_integral P A (P ⊗[R] k)
    _ = ringKrullDim (MvPolynomial (Fin n) k) := ringKrullDim_eq_of_ringEquiv e'
    _ = n := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

end GroupActions
