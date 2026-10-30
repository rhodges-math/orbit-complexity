import OrbitComplexity.FrobeniusSplitting.Normality.NormalizationOpen
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Finite algebras over normal fibres

A finite algebra which agrees with its normal base after inverting a regular
denominator equals its base. Finite normalization supplies such a denominator
and a commuting localization isomorphism.
-/

set_option autoImplicit false
noncomputable section
namespace FrobeniusSplitting
universe u

open private awayMap_bijective
  from OrbitComplexity.FrobeniusSplitting.Normality.NormalizationOpen

private theorem fraction_algebra_surjective {A B : Type u}
    [CommRing A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f) :
    Function.Surjective (algebraMap A B) := by
  intro b
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.map f (IsIntegral.of_finite (R := A) b))
  refine ⟨a, hf ?_⟩
  rw [f.commutes]
  exact ha

/-- A finite algebra over a normal domain equals its base if a regular
denominator gives a commuting isomorphism of the two localizations. The finite
algebra may have zero divisors or be the zero ring. -/
theorem finite_localization_surjective {A B C D : Type u}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [CommRing C] [Algebra A C] [CommRing D] [Algebra B D]
    (d : A) [IsLocalization.Away d C]
    [IsLocalization.Away (algebraMap A B d) D]
    (hd : IsRegular (algebraMap A B d)) (E : C ≃+* D)
    (hE : E.toRingHom.comp (algebraMap A C) =
      (algebraMap B D).comp (algebraMap A B)) :
    Function.Surjective (algebraMap A B) := by
  by_cases hdA : d = 0
  · have hzero : IsRegular (0 : B) := by simpa only [hdA, map_zero] using hd
    intro b
    have hb : b = 0 := hzero.left (by simp)
    exact ⟨0, by simpa only [map_zero] using hb.symm⟩
  have hdK : algebraMap A (FractionRing A) d ≠ 0 := by
    intro h
    apply hdA
    exact IsFractionRing.injective A (FractionRing A) (by simpa only [map_zero] using h)
  let μ : C →ₐ[A] FractionRing A := IsLocalization.Away.liftAlgHom d
    (f := Algebra.ofId A (FractionRing A)) (isUnit_iff_ne_zero.mpr hdK)
  have hμ : Function.Injective μ :=
    IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers d) C μ.toRingHom (by
        intro a ha
        have haK : algebraMap A (FractionRing A) a = 0 := by
          rw [← μ.commutes a]
          exact ha
        have ha0 : a = 0 :=
          IsFractionRing.injective A (FractionRing A) (by simpa only [map_zero] using haK)
        simp only [ha0, map_zero])
  have hBD : Function.Injective (algebraMap B D) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers (algebraMap A B d)) D (by
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      exact hd.pow n)
  let f : B →ₐ[A] FractionRing A :=
    { __ := μ.toRingHom.comp (E.symm.toRingHom.comp (algebraMap B D))
      commutes' a := by
        change μ (E.symm (algebraMap B D (algebraMap A B a))) =
          algebraMap A (FractionRing A) a
        have hEa : E (algebraMap A C a) = algebraMap B D (algebraMap A B a) :=
          RingHom.congr_fun hE a
        rw [← hEa, E.symm_apply_apply]
        exact μ.commutes a }
  have hf : Function.Injective f := hμ.comp (E.symm.injective.comp hBD)
  exact fraction_algebra_surjective f hf

/-- A finite intermediate algebra in a fraction field admits a nonzero
denominator and a commuting isomorphism after inverting it. -/
theorem finite_fraction_localization {A B : Type u}
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra B (FractionRing A)] [IsScalarTower A B (FractionRing A)]
    [FaithfulSMul B (FractionRing A)] [Module.Finite A B] :
    ∃ d : A, d ≠ 0 ∧
      ∃ E : Localization.Away d ≃+* Localization.Away (algebraMap A B d),
        E.toRingHom.comp (algebraMap A (Localization.Away d)) =
          (algebraMap B (Localization.Away (algebraMap A B d))).comp (algebraMap A B) := by
  obtain ⟨c, hc⟩ := exists_mem_conductor (A := A) (B := B) (K := FractionRing A)
    (nonZeroDivisors A)
  have hi : Function.Injective (algebraMap A B) := by
    intro a b h
    apply IsFractionRing.injective A (FractionRing A)
    simpa only [IsScalarTower.algebraMap_apply A B (FractionRing A)] using
      congrArg (algebraMap B (FractionRing A)) h
  let E := RingEquiv.ofBijective (Localization.awayMap (algebraMap A B) (c : A))
    (awayMap_bijective hi (c : A) hc)
  refine ⟨c, nonZeroDivisors.ne_zero c.property, E, ?_⟩
  apply RingHom.ext
  intro a
  change Localization.awayMap (algebraMap A B) (c : A)
    (algebraMap A (Localization.Away (c : A)) a) =
      algebraMap B (Localization.Away (algebraMap A B (c : A))) (algebraMap A B a)
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

/-- The finite normalization of a finite-type domain over a field agrees with
the domain after inverting one explicitly chosen nonzero denominator. -/
theorem normalization_localization {K A : Type u} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ d : A, d ≠ 0 ∧
      ∃ E : Localization.Away d ≃+*
          Localization.Away (algebraMap A (integralClosure A (FractionRing A)) d),
        E.toRingHom.comp (algebraMap A (Localization.Away d)) =
          (algebraMap (integralClosure A (FractionRing A))
            (Localization.Away (algebraMap A (integralClosure A (FractionRing A)) d))).comp
              (algebraMap A (integralClosure A (FractionRing A))) := by
  let : Module.Finite A (integralClosure A (FractionRing A)) :=
    finite_normalization (k := K) (R := A)
  exact finite_fraction_localization (A := A) (B := integralClosure A (FractionRing A))

end FrobeniusSplitting
