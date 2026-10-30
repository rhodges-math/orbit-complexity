import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalizationProperties
import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalFibreSurjectivity
import Batteries.Tactic.Lint

/-! # Normality from arithmetic normalization models

The finite normalization comparison identifies the generic finite map with
the normalization inclusion. Surjectivity on the closed residue fibres then
gives normality of the original affine algebra.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A finite arithmetic model of the normalization proves normality when its
maps on closed positive-characteristic residue fibres are surjective. Both
generic comparisons and their whole map square refer to the integral closure
in the fraction field of the given affine domain. -/
theorem normalization_model_normal {R K A A₀ B₀ : Type u}
    [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R]
    [Field K] [Algebra R K] [FaithfulSMul R K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [CommRing A₀] [CommRing B₀] [Algebra R A₀] [Algebra R B₀]
    [Algebra.FiniteType R A₀]
    (f : A₀ →ₐ[R] B₀) (hfinite : f.Finite)
    (eA : K ⊗[R] A₀ ≃ₐ[K] A)
    (eB : K ⊗[R] B₀ ≃ₐ[K] integralClosure A (FractionRing A))
    (hcommute : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      (IsScalarTower.toAlgHom K A (integralClosure A (FractionRing A))).comp
        eA.toAlgHom)
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
      (ringChar (R ⧸ p.asIdeal)).Prime →
        Function.Surjective (Algebra.TensorProduct.lTensor (S := R ⧸ p.asIdeal)
          (R ⧸ p.asIdeal) f)) :
    IsIntegrallyClosed A := by
  let N := integralClosure A (FractionRing A)
  obtain ⟨_, _, _, hnormal, hinj, _⟩ := normalization_properties (K := K) (A := A)
  let : IsIntegrallyClosed N := hnormal
  let : IsDomain (K ⊗[R] B₀) := MulEquiv.isDomain N eB.toRingEquiv.toMulEquiv
  let : IsIntegrallyClosed (K ⊗[R] B₀) :=
    IsIntegrallyClosed.of_equiv eB.toRingEquiv.symm
  let : Algebra A₀ B₀ := f.toRingHom.toAlgebra
  let : IsScalarTower R A₀ B₀ :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : Module.Finite A₀ B₀ := hfinite
  have hi : Function.Injective (Algebra.TensorProduct.lTensor (S := K) K f) := by
    intro x y h
    apply eA.injective
    apply hinj
    have hx : eB ((Algebra.TensorProduct.lTensor (S := K) K f) x) =
        algebraMap A N (eA x) := DFunLike.congr_fun hcommute x
    have hy : eB ((Algebra.TensorProduct.lTensor (S := K) K f) y) =
        algebraMap A N (eA y) := DFunLike.congr_fun hcommute y
    exact hx.symm.trans ((congrArg eB h).trans hy)
  have hresult := normal_baseChange_of_tensor_fibres
    (R := R) (K := K) (A := A₀) (B := B₀) hi hf
  let : IsIntegrallyClosed (K ⊗[R] A₀) := hresult.2
  exact IsIntegrallyClosed.of_equiv eA.toRingEquiv

end FrobeniusSplitting
