import OrbitComplexity.FrobeniusSplitting.Normality.DenseOpen
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteConductor
import OrbitComplexity.FrobeniusSplitting.Normality.Normalization
import OrbitComplexity.FrobeniusSplitting.Normality.Stalk

/-!
# Dense open subsets of finite normalization

A nonzero conductor element becomes a unit on a dense basic open subset. There
the finite intermediate algebra fills its base ring after localization. The
corresponding morphism of spectra is therefore an isomorphism on that open.
The normalization spectrum has integrally closed domain local rings.

## Main results

* `FrobeniusSplitting.isIsoOverDense_of_finite_fraction`: a dense open isomorphism.
* `FrobeniusSplitting.isIsoOverDense_normalization`: its normalization specialization.
* `FrobeniusSplitting.stalks_normalization`: normality of normalization local rings.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

private theorem awayMap_bijective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B)) (c : A)
    (hc : algebraMap A B c ∈ conductor A (1 : B)) :
    Function.Bijective (Localization.awayMap (algebraMap A B) c) := by
  constructor
  · apply Localization.awayMap_injective_iff.2
    intro a ha
    have ha : a = 0 := hinj (ha.trans (map_zero _).symm)
    exact ⟨0, by rw [ha, mul_zero]⟩
  · apply Localization.awayMap_surjective_iff.2
    rw [mem_conductor_iff, Algebra.adjoin_singleton_one] at hc
    intro b
    obtain ⟨a, ha⟩ := hc b
    refine ⟨a, 1, ?_⟩
    rw [pow_one]
    exact ha

/-- A finite intermediate algebra in the fraction field is an isomorphism over a dense open. -/
theorem isIsoOverDense_of_finite_fraction {A B : Type u}
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra B (FractionRing A)] [IsScalarTower A B (FractionRing A)]
    [FaithfulSMul B (FractionRing A)] [Module.Finite A B] :
    IsIsoOverDense (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨c, hc⟩ := exists_mem_conductor (A := A) (B := B) (K := FractionRing A)
    (nonZeroDivisors A)
  have hc0 : (c : A) ≠ 0 := nonZeroDivisors.ne_zero c.2
  have hinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply IsFractionRing.injective A (FractionRing A)
    exact (IsScalarTower.algebraMap_apply A B (FractionRing A) a).trans
      ((congrArg (algebraMap B (FractionRing A)) hab).trans
        (IsScalarTower.algebraMap_apply A B (FractionRing A) b).symm)
  have hbij := awayMap_bijective hinj (c : A) hc
  refine ⟨PrimeSpectrum.basicOpen (c : A), ?_, ?_⟩
  · apply (PrimeSpectrum.basicOpen (c : A)).isOpen.dense
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    change (c : A) ∉ (⊥ : Ideal A)
    simpa only [Ideal.mem_bot] using hc0
  · have : IsIso (Spec.map (CommRingCat.ofHom
        (Localization.awayMap (algebraMap A B) (c : A)))) :=
      isIso_SpecMap_iff.2 hbij
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap A B)) (c : A))).2
        inferInstance

/-- Finite normalization of an affine variety is an isomorphism over a dense open subset. -/
theorem isIsoOverDense_normalization {K A : Type u} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    IsIsoOverDense (Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A))))) := by
  have := finite_normalization (k := K) (R := A)
  exact isIsoOverDense_of_finite_fraction

end FrobeniusSplitting
