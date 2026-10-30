import OrbitComplexity.FrobeniusSplitting.Normality.Models.RegularNormalizationModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalModelFibres
import OrbitComplexity.FrobeniusSplitting.Normality.Models.LocalizationFibres
import Batteries.Tactic.Lint

/-! # Normality from positive-characteristic model fibres

A prescribed finitely presented coefficient model determines the finite
normalization comparison. Normality of its positive-characteristic field
fibres forces the generic affine domain to be normal.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

private theorem away_square_of_image_eq
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (d : A) (b : B) (hb : f d = b)
    (h : ∃ E : Localization.Away d ≃+* Localization.Away b,
      E.toRingHom.comp (algebraMap A (Localization.Away d)) =
        (algebraMap B (Localization.Away b)).comp f) :
    ∃ E : Localization.Away d ≃+* Localization.Away (f d),
      E.toRingHom.comp (algebraMap A (Localization.Away d)) =
        (algebraMap B (Localization.Away (f d))).comp f := by
  subst b
  exact h

private theorem normal_of_regular_data
    {S R K M A : Type u} [CommRing S] [CommRing R] [IsDomain R]
    [Field K] [CommRing M] [CommRing A] [IsDomain A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S M] [Algebra.FinitePresentation S M] [Algebra K A]
    (eM : K ⊗[S] M ≃ₐ[K] A) (P Q : Prop)
    (hft : P → Algebra.FiniteType ℤ R)
    (hiR : Function.Injective (algebraMap R K))
    (hdata : RegularNormalizationData (R := R) eM
      (IsScalarTower.toAlgHom K A (integralClosure A (FractionRing A))) P Q)
    (hfibres : ∀ (L : Type u) [Field L] [Algebra S L],
      (ringChar L).Prime →
        Subsingleton (L ⊗[S] M) ∨
          (IsDomain (L ⊗[S] M) ∧ IsIntegrallyClosed (L ⊗[S] M))) :
    IsIntegrallyClosed A := by
  obtain ⟨B, hB, f, eB, hP, _, hfinite, hmap, d, _, haway, hregular⟩ := hdata
  let : Algebra.FiniteType ℤ R := hft hP
  let : Algebra.FinitePresentation R B := hB
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hiR
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.equiv eM
  let eA : K ⊗[R] (R ⊗[S] M) ≃ₐ[K] A :=
    (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  obtain ⟨E, hE⟩ := haway
  apply normal_of_localization_fibres f hfinite eA eB hmap d
  intro p hp hprime
  let : p.asIdeal.IsMaximal := hp
  let L := R ⧸ p.asIdeal
  let : Field L := Ideal.Quotient.field p.asIdeal
  let : Algebra S L := inferInstance
  let : IsScalarTower S R L := inferInstance
  have hL := hfibres L hprime
  let EC : L ⊗[R] (R ⊗[S] M) ≃ₐ[L] L ⊗[S] M :=
    Algebra.TensorProduct.cancelBaseChange S R L L M
  have hnormal : Subsingleton (L ⊗[R] (R ⊗[S] M)) ∨
      (IsDomain (L ⊗[R] (R ⊗[S] M)) ∧
        IsIntegrallyClosed (L ⊗[R] (R ⊗[S] M))) := by
    rcases hL with hzero | ⟨hdom, hclosed⟩
    · let : Subsingleton (L ⊗[S] M) := hzero
      exact Or.inl ⟨fun x y => EC.injective (Subsingleton.elim _ _)⟩
    · let : IsDomain (L ⊗[S] M) := hdom
      let : IsIntegrallyClosed (L ⊗[S] M) := hclosed
      exact Or.inr ⟨MulEquiv.isDomain _ EC.toRingEquiv.toMulEquiv,
        IsIntegrallyClosed.of_equiv EC.toRingEquiv.symm⟩
  have hloc := localization_baseChange_equiv (R := R) (L := L) f d E hE
  refine ⟨hnormal, ?_, ?_⟩
  · simpa only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply] using hregular L
  · have hb : (Algebra.TensorProduct.lTensor (S := L) L f) ((1 : L) ⊗ₜ[R] d) =
        (1 : L) ⊗ₜ[R] f d := by
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
    exact away_square_of_image_eq
      (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom
      ((1 : L) ⊗ₜ[R] d) ((1 : L) ⊗ₜ[R] f d) hb hloc

/-- An affine domain is normal if every positive-characteristic field fibre of
a prescribed finitely presented coefficient model is either empty or normal.
The finite normalization, denominator and all model comparisons are constructed
from the prescribed generic comparison. -/
theorem normal_of_positive_model_fibres {K A M : Type u}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [CommRing M]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra.FinitePresentation S M]
    (eM : K ⊗[S] M ≃ₐ[K] A)
    (hfibres : ∀ (L : Type u) [Field L] [Algebra S L],
      (ringChar L).Prime →
        Subsingleton (L ⊗[S] M) ∨
          (IsDomain (L ⊗[S] M) ∧ IsIntegrallyClosed (L ⊗[S] M))) :
    IsIntegrallyClosed A := by
  obtain ⟨R, hSR, hdata⟩ := exists_regular_normalization_model S hS eM S hS
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact normal_of_regular_data (S := S) (R := R) (K := K) eM R.FG (S ≤ R)
    (fun hR => (R.fg_iff_finiteType).1 hR)
    (show Function.Injective (algebraMap R K) from Subtype.val_injective)
    hdata hfibres

end FrobeniusSplitting
