import OrbitComplexity.FrobeniusSplitting.Normality.Models.NormalAlgebraStages
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Batteries.Tactic.Lint

/-! # Algebraic properties of finite normalization

The integral closure of a finite-type domain in its fraction field is finite,
finitely presented over the ground field, and normal. A single denominator
identifies its localization with that of the domain.
-/

set_option autoImplicit false

noncomputable section

namespace FrobeniusSplitting

universe u

/-- The integral closure of a finite-type domain has finite presentation,
is a normal domain, and agrees with the domain after inverting a nonzero
element whose image is regular. The localization retains the source map. -/
theorem normalization_properties {K A : Type u} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    let N := integralClosure A (FractionRing A)
    Module.Finite A N ∧ Algebra.FinitePresentation K N ∧ IsDomain N ∧
      IsIntegrallyClosed N ∧ Function.Injective (algebraMap A N) ∧
      ∃ d : A, d ≠ 0 ∧ IsRegular (algebraMap A N d) ∧
        ∃ E : Localization.Away d ≃+* Localization.Away (algebraMap A N d),
          E.toRingHom.comp (algebraMap A (Localization.Away d)) =
            (algebraMap N (Localization.Away (algebraMap A N d))).comp
              (algebraMap A N) := by
  let N := integralClosure A (FractionRing A)
  let : Module.Finite A N := finite_normalization (k := K) (R := A)
  let : Algebra.FiniteType A N := inferInstance
  let : Algebra.FiniteType K N :=
    Algebra.FiniteType.trans (R := K) (S := A) (A := N) inferInstance inferInstance
  have hfp : Algebra.FinitePresentation K N :=
    (Algebra.FinitePresentation.of_finiteType (R := K) (A := N)).1 inferInstance
  have hnormal : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := A) (K := FractionRing A) (L := FractionRing A)
  have hi : Function.Injective (algebraMap A N) := by
    intro a b h
    apply IsFractionRing.injective A (FractionRing A)
    exact congrArg (fun n : N => (n : FractionRing A)) h
  obtain ⟨d, hd, E, hE⟩ := normalization_localization (K := K) (A := A)
  have hregular : IsRegular (algebraMap A N d) := by
    apply IsRegular.of_ne_zero
    intro h
    apply hd
    apply hi
    exact h.trans (map_zero (algebraMap A N)).symm
  exact ⟨inferInstance, hfp, inferInstance, hnormal, hi, d, hd, hregular, E, hE⟩

end FrobeniusSplitting
