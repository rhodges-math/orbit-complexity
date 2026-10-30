import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalAlgebraStages
import OrbitComplexity.FrobeniusSplitting.Normality.GenericBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Surjectivity from normal closed fibres

The finite localization criterion allows zero source rings. Tensor-fibre
surjectivity supplies element lifts in quotient fibres and hence the generic
normality criterion over characteristic zero.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u v

/-- A finite ring map which is an isomorphism after inverting a denominator
regular in the target is surjective when the source is either zero or an
integrally closed domain. -/
theorem finite_localization_surj_or_zero {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (hf : f.Finite)
    (hn : Subsingleton A ∨ (IsDomain A ∧ IsIntegrallyClosed A))
    [Algebra A C] [Algebra B D] (d : A) [IsLocalization.Away d C]
    [IsLocalization.Away (f d) D]
    (hd : IsRegular (f d)) (E : C ≃+* D)
    (hE : E.toRingHom.comp (algebraMap A C) = (algebraMap B D).comp f) :
    Function.Surjective f := by
  rcases hn with hzero | ⟨hdomain, hnormal⟩
  · let : Subsingleton A := hzero
    have hB : (0 : B) = 1 :=
      f.map_zero.symm.trans ((congrArg f (Subsingleton.elim (0 : A) 1)).trans f.map_one)
    let : Subsingleton B := subsingleton_of_zero_eq_one hB
    intro b
    exact ⟨0, Subsingleton.elim _ _⟩
  · let : IsDomain A := hdomain
    let : IsIntegrallyClosed A := hnormal
    let : Algebra A B := f.toAlgebra
    let : Module.Finite A B := hf
    exact finite_localization_surjective d hd E hE

/-- Surjectivity of a tensor fibre map gives lifts of all target elements modulo
the extended coefficient ideal. -/
theorem quotient_lifts_of_tensor_surjective {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R)
    (hf : Function.Surjective
      (Algebra.TensorProduct.lTensor (S := R ⧸ I) (R ⧸ I) f)) :
    ∀ b : B, ∃ a : A,
      Ideal.Quotient.mk (I.map (algebraMap R B)) b =
        Ideal.Quotient.mk (I.map (algebraMap R B)) (f a) := by
  intro b
  let EA := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  let EB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  obtain ⟨t, ht⟩ := hf ((1 : R ⧸ I) ⊗ₜ[R] b)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (EA.symm t)
  have hat : (1 : R ⧸ I) ⊗ₜ[R] a = t := by
    calc
      (1 : R ⧸ I) ⊗ₜ[R] a = EA (Ideal.Quotient.mk (I.map (algebraMap R A)) a) :=
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A I a).symm
      _ = EA (EA.symm t) := congrArg EA ha
      _ = t := EA.apply_symm_apply t
  refine ⟨a, ?_⟩
  apply EB.injective
  simp only [EB, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  exact ht.symm.trans (congrArg
    (Algebra.TensorProduct.lTensor (S := R ⧸ I) (R ⧸ I) f) hat.symm)

/-- Surjective closed tensor fibres and an injective generic map identify the
generic source with its normal finite extension. -/
theorem normal_baseChange_of_tensor_fibres {R A B : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [Field K]
    [Algebra R K] [FaithfulSMul R K] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    [IsDomain (K ⊗[R] B)] [IsIntegrallyClosed (K ⊗[R] B)]
    (hi : Function.Injective (Algebra.TensorProduct.lTensor (S := K) K
      (IsScalarTower.toAlgHom R A B)))
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal → (ringChar (R ⧸ p.asIdeal)).Prime →
      Function.Surjective (Algebra.TensorProduct.lTensor (S := R ⧸ p.asIdeal)
        (R ⧸ p.asIdeal) (IsScalarTower.toAlgHom R A B))) :
    IsDomain (K ⊗[R] A) ∧ IsIntegrallyClosed (K ⊗[R] A) := by
  exact normal_baseChange_of_closed_fibers hi (fun p hp hchar =>
    quotient_lifts_of_tensor_surjective (IsScalarTower.toAlgHom R A B) p.asIdeal
      (hf p hp hchar))

end FrobeniusSplitting
