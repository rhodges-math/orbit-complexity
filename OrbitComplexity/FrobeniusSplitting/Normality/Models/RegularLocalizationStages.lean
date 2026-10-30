import OrbitComplexity.FrobeniusSplitting.Normality.Models.RegularModelStages
import OrbitComplexity.FrobeniusSplitting.Normality.Models.LocalizationFibres
import Batteries.Tactic.Lint

/-! # Regular localization comparisons at coefficient extensions

A retained localization comparison survives a coefficient extension where
the target algebra and the denominator quotient become free. Its denominator
then stays regular over every further coefficient algebra.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

private theorem scalar_away_comparison
    {S R A B : Type u} [CommRing S] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (d : A)
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (f d))).comp f.toRingHom) :
    ∃ ER : Localization.Away ((1 : R) ⊗ₜ[S] d) ≃+*
        Localization.Away ((1 : R) ⊗ₜ[S] f d),
      ER.toRingHom.comp (algebraMap (R ⊗[S] A)
        (Localization.Away ((1 : R) ⊗ₜ[S] d))) =
        (algebraMap (R ⊗[S] B) (Localization.Away ((1 : R) ⊗ₜ[S] f d))).comp
          (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom := by
  exact localization_baseChange_equiv (R := S) (L := R) f d E hE

/-- A coefficient extension retaining the comparison on the target algebra,
free target and principal quotient, an exact localization square, and
regularity of the denominator after every further scalar extension. -/
def RegularLocalizationData
    {S R K A B N : Type u} [CommRing S] [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [CommRing N]
    [Algebra S R] [Algebra S K] [Algebra R K] [Algebra S A] [Algebra S B]
    [Algebra K N] (f : A →ₐ[S] B) (e : K ⊗[S] B ≃ₐ[K] N) (d : A)
    (P Q : Prop) : Prop :=
    ∃ eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] N,
      P ∧ Q ∧ Module.Free R (R ⊗[S] B) ∧
      Module.Free R ((R ⊗[S] B) ⧸
        Ideal.span ({(1 : R) ⊗ₜ[S] f d} : Set (R ⊗[S] B))) ∧
      (∀ b : B, eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] b)) = e ((1 : K) ⊗ₜ[S] b)) ∧
      (∃ ER : Localization.Away ((1 : R) ⊗ₜ[S] d) ≃+*
          Localization.Away ((1 : R) ⊗ₜ[S] f d),
        ER.toRingHom.comp (algebraMap (R ⊗[S] A)
          (Localization.Away ((1 : R) ⊗ₜ[S] d))) =
          (algebraMap (R ⊗[S] B) (Localization.Away ((1 : R) ⊗ₜ[S] f d))).comp
            (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom) ∧
      ∀ (L : Type u) [CommRing L] [Algebra R L],
        IsRegular ((1 : L) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] f d) : L ⊗[R] (R ⊗[S] B))

private theorem add_localization_comparison
    {S R K A B N : Type u} [CommRing S] [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [CommRing N]
    [Algebra S R] [Algebra S K] [Algebra R K] [Algebra S A] [Algebra S B]
    [Algebra K N] (f : A →ₐ[S] B) (e : K ⊗[S] B ≃ₐ[K] N) (d : A)
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (f d))).comp f.toRingHom)
    (P Q : Prop)
    (h : ∃ eR : K ⊗[R] (R ⊗[S] B) ≃ₐ[K] N,
      P ∧ Q ∧ Module.Free R (R ⊗[S] B) ∧
      Module.Free R ((R ⊗[S] B) ⧸
        Ideal.span ({(1 : R) ⊗ₜ[S] f d} : Set (R ⊗[S] B))) ∧
      (∀ b : B, eR ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] b)) = e ((1 : K) ⊗ₜ[S] b)) ∧
      ∀ (L : Type u) [CommRing L] [Algebra R L],
        IsRegular ((1 : L) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] f d) : L ⊗[R] (R ⊗[S] B))) :
    RegularLocalizationData (S := S) (R := R) (K := K) f e d P Q := by
  obtain ⟨eR, hP, hQ, hfree, hquot, heR, hregular⟩ := h
  have haway := scalar_away_comparison (S := S) (R := R) f d E hE
  exact ⟨eR, hP, hQ, hfree, hquot, heR, haway, hregular⟩

/-- A finite-presentation target and its denominator quotient become free at
one coefficient extension. The exact source localization comparison remains,
and the target denominator is regular over every later coefficient algebra. -/
theorem exists_regular_localization_stage
    {K A B N : Type u} [Field K] [CommRing A] [CommRing B]
    [CommRing N] [Algebra K N]
    (S : Subalgebra ℤ K) (hS : S.FG) [Algebra S A] [Algebra S B]
    [Algebra.FinitePresentation S B]
    (f : A →ₐ[S] B) (e : K ⊗[S] B ≃ₐ[K] N) (d : A)
    (hd : IsRegular (e ((1 : K) ⊗ₜ[S] f d)))
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (f d))).comp f.toRingHom)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      RegularLocalizationData (S := S) (R := R) (K := K)
        f e d R.FG (start ≤ R) := by
  obtain ⟨R, hSR, hdata⟩ :=
    exists_regular_model_stage S hS e (f d) hd start hstart
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  refine ⟨R, hSR, ?_⟩
  exact add_localization_comparison (S := S) (R := R) (K := K)
    f e d E hE R.FG (start ≤ R) hdata

end FrobeniusSplitting
