import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.FiniteCoverOpens
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite covers after coefficient localization -/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u v

/-- A finite field-model cover remains a cover after localizing the coefficient
base when its chart maps and cartesian target comparison are retained. -/
theorem exists_finite_model_cover {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {I : Type v} [Finite I] {Y YK : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (X XK : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y) (fK : ∀ i, XK i ⟶ YK)
    (base : Y ⟶ Spec (.of R))
    [∀ i, LocallyOfFinitePresentation (f i)] [∀ i, QuasiCompact (f i)]
    [LocallyOfFinitePresentation base] [QuasiCompact base]
    (qX : ∀ i, XK i ⟶ X i) (qY : YK ⟶ Y) (baseK : YK ⟶ Spec (.of K))
    (hsq : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hcomm : ∀ i, qX i ≫ f i = fK i ≫ qY)
    (hcoverK : ∀ y : YK, ∃ i x, fK i x = y) :
    ∃ r : R, r ≠ 0 ∧
      ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → ∃ i x, f i x = y := by
  apply exists_finite_cover_base_open X f base
  intro y hy
  let η : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have hmap : ((Spec.map (CommRingCat.ofHom (algebraMap R K))) η).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj
  have heq : base y = (Spec.map (CommRingCat.ofHom (algebraMap R K))) η :=
    PrimeSpectrum.ext (hy.trans hmap.symm)
  obtain ⟨yk, hyk, _⟩ := Scheme.exists_preimage_of_isPullback hsq y η heq
  obtain ⟨i, xk, hxk⟩ := hcoverK yk
  refine ⟨i, qX i xk, ?_⟩
  have h := congrArg (fun z : XK i ⟶ Y ↦ z xk) (hcomm i)
  simpa only [Scheme.Hom.comp_apply, hxk, hyk] using h

end FrobeniusSplitting
