import OrbitComplexity.FrobeniusSplitting.Normality.Components.PrimeWitnessOpens
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Nonvanishing in field fibres over a principal coefficient open -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false

universe u v

namespace FrobeniusSplitting

private theorem away_comap_base
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (x : A) (p : PrimeSpectrum (Localization.Away x)) :
    PrimeSpectrum.comap (algebraMap R A)
      (PrimeSpectrum.comap (algebraMap A (Localization.Away x)) p) =
      PrimeSpectrum.comap (algebraMap R (Localization.Away x)) p := by
  rw [← PrimeSpectrum.comap_comp_apply,
    ← IsScalarTower.algebraMap_eq R A (Localization.Away x)]

private theorem exists_generic_away_point
    {R A K : Type u} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [FaithfulSMul R K]
    (x : A) (hx : ¬ IsNilpotent ((1 : K) ⊗ₜ[R] x)) :
    ∃ p : PrimeSpectrum (Localization.Away x),
      (PrimeSpectrum.comap (algebraMap R (Localization.Away x)) p).asIdeal = ⊥ := by
  classical
  have hex : ∃ p : PrimeSpectrum (K ⊗[R] A),
      (1 : K) ⊗ₜ[R] x ∉ p.asIdeal := by
    by_contra h
    apply hx
    refine nilpotent_iff_mem_prime.mpr ?_
    intro P hP
    by_contra hnot
    exact h ⟨⟨P, hP⟩, hnot⟩
  obtain ⟨pK, hpK⟩ := hex
  let pA := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom pK
  have hzero : (PrimeSpectrum.comap (algebraMap R A) pA).asIdeal = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro r hr
    change r = 0
    by_contra hne
    change (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
      (algebraMap R A r) ∈ pK.asIdeal at hr
    rw [AlgHom.commutes] at hr
    have hK : algebraMap R K r ≠ 0 := fun hz ↦ hne
      ((FaithfulSMul.algebraMap_injective R K)
        (hz.trans (map_zero (algebraMap R K)).symm))
    have hunit : IsUnit (algebraMap R (K ⊗[R] A) r) := by
      rw [IsScalarTower.algebraMap_apply R K (K ⊗[R] A)]
      exact (isUnit_iff_ne_zero.mpr hK).map (algebraMap K (K ⊗[R] A))
    exact pK.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hr hunit)
  have hbasic : pA ∈ PrimeSpectrum.basicOpen x := hpK
  have hrange : pA ∈ Set.range
      (PrimeSpectrum.comap (algebraMap A (Localization.Away x))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away x) x]
    exact hbasic
  obtain ⟨p, hp⟩ := hrange
  refine ⟨p, ?_⟩
  have hcomp : PrimeSpectrum.comap (algebraMap R (Localization.Away x)) p =
      PrimeSpectrum.comap (algebraMap R A) pA :=
    (away_comap_base x p).symm.trans
      (congrArg (PrimeSpectrum.comap (algebraMap R A)) hp)
  exact (congrArg PrimeSpectrum.asIdeal hcomp).trans hzero

private theorem not_nilpotent_tmul_of_prime
    {R A L : Type u} [CommRing R] [CommRing A] [Field L]
    [Algebra R A] [Algebra R L]
    (x : A) (pA : PrimeSpectrum A) (hx : x ∉ pA.asIdeal)
    (hbase : PrimeSpectrum.comap (algebraMap R A) pA =
      PrimeSpectrum.comap (algebraMap R L) ⟨⊥, inferInstance⟩) :
    ¬ IsNilpotent ((1 : L) ⊗ₜ[R] x) := by
  have hsquare := isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap R L))
    (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[R] A))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom)
    (CommRingCat.isPushout_tensorProduct R L A)
  obtain ⟨p, _, hpA⟩ := Scheme.exists_preimage_of_isPullback
    hsquare (⟨⊥, inferInstance⟩ : PrimeSpectrum L) pA hbase.symm
  have hpx : (1 : L) ⊗ₜ[R] x ∉ p.asIdeal := by
    have h := (congrArg (fun q : PrimeSpectrum A ↦ x ∉ q.asIdeal) hpA).mpr hx
    exact h
  intro hnil
  exact hpx (nilpotent_iff_mem_prime.mp hnil p.asIdeal p.isPrime)

/-- Finitely many elements nonnilpotent over a faithful field stay nonnilpotent
over every field whose coefficient point lies in one nonempty principal open. -/
theorem exists_fiber_nonvanishing_open
    {R K : Type u} [hR : CommRing R] [hdom : IsDomain R] [Field K]
    [Algebra R K] [FaithfulSMul R K]
    {I : Type v} [hI : Finite I] (A : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)]
    (x : ∀ i, A i) (hx : ∀ i, ¬ IsNilpotent ((1 : K) ⊗ₜ[R] x i)) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (L : Type u) [Field L] [Algebra R L], algebraMap R L r ≠ 0 →
        ∀ i, ¬ IsNilpotent ((1 : L) ⊗ₜ[R] x i) := by
  let X : I → Scheme.{u} := fun i ↦ Spec (.of (Localization.Away (x i)))
  let Y : I → Scheme.{u} := fun _ ↦ Spec (.of R)
  let f : ∀ i, X i ⟶ Y i := fun i ↦
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x i))))
  let base : ∀ i, Y i ⟶ Spec (.of R) := fun _ ↦ 𝟙 _
  have hcompact : ∀ i, CompactSpace (Y i) := fun _ ↦ inferInstance
  have hqs : ∀ i, QuasiSeparatedSpace (Y i) := fun _ ↦ inferInstance
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := by
    intro i
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hqc : ∀ i, QuasiCompact (f i) := fun _ ↦ inferInstance
  have hbfp : ∀ i, LocallyOfFinitePresentation (base i) := fun _ ↦ inferInstance
  have hbqc : ∀ i, QuasiCompact (base i) := fun _ ↦ inferInstance
  have hgeneric : ∀ i (y : Y i), (base i y).asIdeal = ⊥ →
      y ∈ Set.range (f i) := by
    intro i y hy
    obtain ⟨p, hp⟩ := exists_generic_away_point (x i) (hx i)
    exact ⟨p, PrimeSpectrum.ext (hp.trans hy.symm)⟩
  have hopen := @exists_finite_surjective_base_open.{u, v}
    R hR hdom I hI X Y hcompact hqs f base hfp hqc hbfp hbqc hgeneric
  obtain ⟨r, hr, hsurj⟩ := hopen
  refine ⟨r, hr, ?_⟩
  intro L _ _ hrL i
  have hropen : PrimeSpectrum.comap (algebraMap R L)
      (⟨⊥, inferInstance⟩ : PrimeSpectrum L) ∈ PrimeSpectrum.basicOpen r := by
    change algebraMap R L r ∉ (⊥ : Ideal L)
    simpa only [Ideal.mem_bot] using hrL
  obtain ⟨p, hp⟩ := hsurj i
    (PrimeSpectrum.comap (algebraMap R L) ⟨⊥, inferInstance⟩) hropen
  let pA := PrimeSpectrum.comap (algebraMap (A i) (Localization.Away (x i))) p
  have hxA : x i ∉ pA.asIdeal := by
    have hpA : pA ∈ Set.range
        (PrimeSpectrum.comap (algebraMap (A i) (Localization.Away (x i)))) := ⟨p, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (x i)) (x i)] at hpA
    exact hpA
  have hbase : PrimeSpectrum.comap (algebraMap R (A i)) pA =
      PrimeSpectrum.comap (algebraMap R L) ⟨⊥, inferInstance⟩ :=
    (away_comap_base (x i) p).trans hp
  have h := not_nilpotent_tmul_of_prime (x i) pA hxA hbase
  exact h

end FrobeniusSplitting
