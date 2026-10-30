import OrbitComplexity.FrobeniusSplitting.Normality.ConductorLocalization
import OrbitComplexity.FrobeniusSplitting.Normality.MinimalPrime
import OrbitComplexity.FrobeniusSplitting.Normality.Quotient
import OrbitComplexity.FrobeniusSplitting.Splittings.Localization
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.Algebra.CharP.Basic

/-!
# Finite universally injective extensions

A finite algebra embedded in a ring with a compatible Frobenius splitting equals
the image of its base when the induced map on spectra is universally injective.
The proof localizes at a minimal prime over the conductor, passes to residue
fields, and uses Frobenius root closure.

## References

* Brion and Kumar, *Frobenius splitting methods in geometry and representation
  theory*, Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory IsLocalization

universe u

/-- The base fills the localized algebra at a minimal conductor prime. -/
theorem surjective_at_conductor {A B : Type u} {K : Type*}
    [CommRing A] [CommRing B] [CommRing K] [Algebra A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] [FaithfulSMul B K] {q : ℕ} [Fact q.Prime] [CharP A q]
    (base : RingSplitting A q) (ambient : RingSplitting K q)
    (hcommute : ∀ a, ambient (algebraMap A K a) = algebraMap A K (base a))
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (prime : Ideal A) [prime.IsPrime]
    (hprime : prime ∈ ((conductor A (1 : B)).comap (algebraMap A B)).minimalPrimes) :
    Function.Surjective (algebraMap (Localization.AtPrime prime)
      (Localization (Algebra.algebraMapSubmonoid B prime.primeCompl))) := by
  let M := prime.primeCompl
  let N := Algebra.algebraMapSubmonoid B M
  let L := Algebra.algebraMapSubmonoid K M
  let Aₚ := Localization.AtPrime prime
  let Bₚ := Localization N
  let Kₚ := Localization L
  have : IsLocalization (Algebra.algebraMapSubmonoid K N) Kₚ := by
    change IsLocalization (N.map (IsScalarTower.toAlgHom A B K).toRingHom) Kₚ
    infer_instance
  let : Algebra Bₚ Kₚ := localizationAlgebra N K
  have : IsScalarTower B Bₚ Kₚ := isScalarTower_localizationAlgebra N K
  let f := algebraMap Aₚ Bₚ
  let j := algebraMap Bₚ Kₚ
  let C := conductor A (1 : B)
  let I := C.comap (algebraMap A B)
  let J := C.map (algebraMap B Bₚ)
  have hp : 1 < q := (Fact.out : q.Prime).one_lt
  have hpzero : 0 < q := Nat.zero_lt_one.trans hp
  let baseₚ := base.localize (S := Aₚ) M hpzero
  let ambientₚ := ambient.localize (S := Kₚ) L hpzero
  have hbase : Set.MapsTo ambient (⊥ : Subalgebra A K) (⊥ : Subalgebra A K) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨base a, (hcommute a).symm⟩
  have hC : C.IsRadical := conductor_isRadical ambient hbase hp
  have hI : I.IsRadical := hC.comap (algebraMap A B)
  have hCimage : (C : Set B) ⊆ Set.range (algebraMap A B) := by
    intro b hb
    change b ∈ (⊥ : Subalgebra A B)
    have hmem := conductor_subset_adjoin hb
    rw [Algebra.adjoin_singleton_one] at hmem
    change b ∈ (⊥ : Subalgebra A B) at hmem
    exact hmem
  have hJimage : (J : Set Bₚ) ⊆ Set.range f :=
    map_subset_range_localization M C hCimage
  have hcomap : J.comap f = I.map (algebraMap A Aₚ) := comap_map_localization M C
  have hsource : IsField (Aₚ ⧸ J.comap f) := by
    rw [hcomap]
    exact isField_quotient_at_minimalPrime I prime hI hprime
  let := hsource.toField
  have hJ : J.IsRadical := by
    apply Ideal.radical_eq_iff.1
    rw [← IsLocalization.map_radical N Bₚ, hC.radical]
  have : IsReduced (Bₚ ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  have hlocalization : IsPreimmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B Bₚ))) :=
    IsPreimmersion.of_isLocalization N
  have hsquare :
      Spec.map (CommRingCat.ofHom f) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Aₚ)) =
      Spec.map (CommRingCat.ofHom (algebraMap B Bₚ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (IsScalarTower.algebraMap_apply A Aₚ Bₚ a).symm.trans
      (IsScalarTower.algebraMap_apply A B Bₚ a)
  have hcomposite : UniversallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap B Bₚ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  rw [← hsquare] at hcomposite
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom f)) :=
    universallyInjective_of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap A Aₚ)))
  have : UniversallyInjective (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J f le_rfl))) := quotientMap_universallyInjective f J
  have : Nontrivial (Bₚ ⧸ J) := (Ideal.quotientMap_injective (I := J) (f := f)).nontrivial
  have htarget : IsField (Bₚ ⧸ J) :=
    isField_of_universallyInjective (Ideal.quotientMap J f le_rfl)
  have : CharP (Aₚ ⧸ J.comap f) q :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).2 (by
      have hzero := congrArg ((Ideal.Quotient.mk (J.comap f)).comp (algebraMap A Aₚ))
        (CharP.cast_eq_zero A q)
      simpa only [map_natCast, map_zero] using hzero)
  have hinjective : Function.Injective j :=
    localizationAlgebra_injective (M := N) (S := K) Bₚ Kₚ
      (FaithfulSMul.algebraMap_injective B K)
  have htower (a : A) : j (f (algebraMap A Aₚ a)) =
      algebraMap K Kₚ (algebraMap A K a) := by
    calc
      j (f (algebraMap A Aₚ a)) = j (algebraMap A Bₚ a) := by
        rw [← IsScalarTower.algebraMap_apply A Aₚ Bₚ]
      _ = j (algebraMap B Bₚ (algebraMap A B a)) := by
        rw [IsScalarTower.algebraMap_apply A B Bₚ]
      _ = algebraMap B Kₚ (algebraMap A B a) := by
        rw [← IsScalarTower.algebraMap_apply B Bₚ Kₚ]
      _ = algebraMap K Kₚ (algebraMap B K (algebraMap A B a)) := by
        rw [IsScalarTower.algebraMap_apply B K Kₚ]
      _ = algebraMap K Kₚ (algebraMap A K a) := by
        rw [← IsScalarTower.algebraMap_apply A B K]
  have hcommuteₚ (a : Aₚ) : ambientₚ (j (f a)) = j (f (baseₚ a)) := by
    apply RingSplitting.map_localize M base hpzero ambientₚ (j.comp f)
    intro a
    change ambientₚ (j (f (algebraMap A Aₚ a))) = j (f (algebraMap A Aₚ (base a)))
    rw [htower, RingSplitting.localize_algebraMap, hcommute, htower]
  apply surjective_of_quotientMap f J hJimage
  exact baseₚ.quotient_surjective_of_specMap ambientₚ f j hinjective hcommuteₚ
    J hJimage hsource htarget

/-- A finite algebra universally injective on spectra is filled by an embedded split base. -/
theorem surjective_of_finite_specMap {A B : Type u} {K : Type*}
    [CommRing A] [CommRing B] [CommRing K] [Algebra A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] [FaithfulSMul B K] [Module.Finite A B]
    {q : ℕ} [Fact q.Prime] [CharP A q]
    (base : RingSplitting A q) (ambient : RingSplitting K q)
    (hcommute : ∀ a, ambient (algebraMap A K a) = algebraMap A K (base a))
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    Function.Surjective (algebraMap A B) := by
  let C := conductor A (1 : B)
  let I := C.comap (algebraMap A B)
  have hItop : I = ⊤ := by
    by_contra hI
    obtain ⟨⟨prime, hprime⟩⟩ := Ideal.nonempty_minimalPrimes hI
    have := hprime.isPrime
    have hsupport : (⟨prime, hprime.isPrime⟩ : PrimeSpectrum A) ∈
        Module.support A (B ⧸ (⊥ : Subalgebra A B).toSubmodule) :=
      (mem_support_quotient_iff ⟨prime, hprime.isPrime⟩).2 hprime.le
    have hsurjective := surjective_at_conductor base ambient hcommute prime hprime
    have hsubsingleton := subsingleton_quotient_of_surjective
      (A := A) (B := B)
      (Aₘ := Localization.AtPrime prime)
      (Bₘ := Localization (Algebra.algebraMapSubmonoid B prime.primeCompl))
      prime.primeCompl hsurjective
    exact (not_nontrivial_iff_subsingleton.2 hsubsingleton) hsupport
  have hone : (1 : B) ∈ C := by
    have hmem : (1 : A) ∈ I := by rw [hItop]; trivial
    change algebraMap A B 1 ∈ C at hmem
    simpa only [map_one] using hmem
  intro b
  change b ∈ (⊥ : Subalgebra A B)
  have hmem := mem_conductor_iff.1 hone b
  rw [one_mul, Algebra.adjoin_singleton_one] at hmem
  change b ∈ (⊥ : Subalgebra A B) at hmem
  exact hmem

end FrobeniusSplitting
