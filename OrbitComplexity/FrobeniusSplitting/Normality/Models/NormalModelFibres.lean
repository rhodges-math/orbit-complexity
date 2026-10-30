import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalizationDescent
import Mathlib.RingTheory.TensorProduct.Finite
import Batteries.Tactic.Lint

/-! # Residue localization criteria for arithmetic normality

A finite normalization model is surjective on a residue fibre when that
fibre's source is normal and the denominator is regular in its target.
The same statement includes empty affine fibres.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

private theorem finite_lTensor {R L A B : Type u}
    [CommRing R] [CommRing L] [CommRing A] [CommRing B]
    [Algebra R L] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : f.Finite) :
    (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom.Finite := by
  have hid : (AlgHom.id R L).Finite := RingHom.Finite.id L
  exact RingHom.Finite.tensorProductMap hid hf

/-- Normal or empty source fibres, together with the localization
comparison and a regular target denominator, make an arithmetic normalization
model surjective on closed fibres and prove normality of the affine domain. -/
theorem normal_of_localization_fibres {R K A A₀ B₀ : Type u}
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
    (d : A₀)
    (hfibres : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
      (ringChar (R ⧸ p.asIdeal)).Prime →
      let L := R ⧸ p.asIdeal
      let AL := L ⊗[R] A₀
      let BL := L ⊗[R] B₀
      let fL : AL →ₐ[L] BL := Algebra.TensorProduct.lTensor (S := L) L f
      let dL : AL := (1 : L) ⊗ₜ[R] d
      (Subsingleton AL ∨ (IsDomain AL ∧ IsIntegrallyClosed AL)) ∧
        IsRegular (fL dL) ∧
        ∃ E : Localization.Away dL ≃+* Localization.Away (fL dL),
          E.toRingHom.comp (algebraMap AL (Localization.Away dL)) =
            (algebraMap BL (Localization.Away (fL dL))).comp fL.toRingHom) :
    IsIntegrallyClosed A := by
  apply normalization_model_normal f hfinite eA eB hcommute
  intro p hp hprime
  obtain ⟨hn, hd, E, hE⟩ := hfibres p hp hprime
  exact finite_localization_surj_or_zero
    (Algebra.TensorProduct.lTensor (S := R ⧸ p.asIdeal)
      (R ⧸ p.asIdeal) f).toRingHom
    (finite_lTensor f hfinite) hn ((1 : R ⧸ p.asIdeal) ⊗ₜ[R] d) hd E hE

end FrobeniusSplitting
