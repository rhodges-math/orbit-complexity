import OrbitComplexity.GroupActions.Rosenlicht.PolynomialLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Fraction coefficients after principal localization

The fraction field of a domain is also the fraction field of every nonzero
principal localization. Polynomial coefficient extension remains a localization
at denominators from the original domain.
-/

open MvPolynomial
open scoped nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) [CommRing R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The fraction-field embedding of a principal localization preserves scalars
from the original ring. -/
def fractionAwayAlgHom (r : R) (hr : r ≠ 0) : Localization.Away r →ₐ[R] F where
  __ := fractionAwayMap R F r hr
  commutes' := fractionAwayMap_algebraMap R F r hr

/-- The fraction field of a domain is the fraction field of its localization
at a nonzero element, for the canonical coefficient embedding. -/
theorem fractionAway_isFractionRing (r : R) (hr : r ≠ 0) :
    let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
    IsFractionRing (Localization.Away r) F := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R F)
    (IsFractionRing.injective R F)
  let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
  let : IsScalarTower R (Localization.Away r) F :=
    IsScalarTower.of_algHom (fractionAwayAlgHom R F r hr)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers r) (Localization.Away r) F

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial extension from a principal localization to the fraction field
is localization at denominators from the original ring. -/
theorem fractionAway_polynomialLocalization {σ : Type w} (r : R) (hr : r ≠ 0) :
    let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial σ (Localization.Away r))
        (nonZeroDivisors R)) (MvPolynomial σ F) := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R F)
    (IsFractionRing.injective R F)
  let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
  let : IsScalarTower R (Localization.Away r) F :=
    IsScalarTower.of_algHom (fractionAwayAlgHom R F r hr)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := by
    rw [Submonoid.powers_le]
    rwa [mem_nonZeroDivisors_iff_ne_zero]
  let : IsLocalization ((nonZeroDivisors R).map
      (algebraMap R (Localization.Away r))) F :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away r) F
      (Submonoid.powers r) (nonZeroDivisors R) hle
  have h := MvPolynomial.isLocalization (σ := σ)
    ((nonZeroDivisors R).map (algebraMap R (Localization.Away r))) F
  convert h using 1
  change (nonZeroDivisors R).map
      (algebraMap R (MvPolynomial σ (Localization.Away r))) = _
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨algebraMap R (Localization.Away r) x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end

end GroupActions
