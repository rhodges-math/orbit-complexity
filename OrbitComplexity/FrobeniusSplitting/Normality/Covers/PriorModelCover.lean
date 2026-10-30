import OrbitComplexity.FrobeniusSplitting.Normality.Covers.FiniteCoverModels

/-! # Coverage on the same prior model after coefficient extension -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v
namespace FrobeniusSplitting

private theorem cover_after_unit {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    {I : Type v} {Y : Scheme.{u}} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y)
    (base : Y ⟶ Spec (.of R)) (r : R) (hr : IsUnit (algebraMap R T r))
    (hcover : ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → ∃ i x, f i x = y) :
    ∀ y : (pullback base (Spec.map (CommRingCat.ofHom (algebraMap R T))) : Scheme.{u}),
      ∃ i, ∃ z : (pullback (f i) (pullback.fst base
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))) : Scheme.{u}),
        (pullback.snd (f i) (pullback.fst base
          (Spec.map (CommRingCat.ofHom (algebraMap R T))))) z = y := by
  intro y
  let a := Spec.map (CommRingCat.ofHom (algebraMap R T))
  have hbase : base ((pullback.fst base a) y) ∈ PrimeSpectrum.basicOpen r := by
    have h := congrArg (fun z : pullback base a ⟶ Spec (.of R) ↦ z y)
      (pullback.condition (f := base) (g := a))
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    let t : PrimeSpectrum T := (pullback.snd base a) y
    exact fun hm ↦ t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hr)
  obtain ⟨i, x, hx⟩ := hcover ((pullback.fst base a) y) hbase
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
  exact ⟨i, z, hz⟩

/-- A retained generic cover covers the same prior model after every extension
inverting one coefficient, including nonreduced and empty scalar fibres. -/
theorem exists_prior_cover_denominator {R K : Type u} [CommRing R] [IsDomain R]
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
    ∃ r : R, r ≠ 0 ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
      IsUnit (algebraMap R T r) →
      ∀ y : (pullback base (Spec.map (CommRingCat.ofHom (algebraMap R T))) : Scheme.{u}),
        ∃ i, ∃ z : (pullback (f i) (pullback.fst base
            (Spec.map (CommRingCat.ofHom (algebraMap R T)))) : Scheme.{u}),
          (pullback.snd (f i) (pullback.fst base
            (Spec.map (CommRingCat.ofHom (algebraMap R T))))) z = y := by
  obtain ⟨r, hr, hcover⟩ := exists_finite_model_cover hinj X XK f fK base qX qY baseK
    hsq hcomm hcoverK
  exact ⟨r, hr, fun T _ _ hunit ↦ cover_after_unit X f base r hunit hcover⟩

end FrobeniusSplitting
