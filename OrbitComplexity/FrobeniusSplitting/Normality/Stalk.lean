import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Normal local rings from affine coordinate charts

Stalks on an affine open subset are localizations of its coordinate ring. Integral
closedness therefore passes from integrally closed domain coordinate rings to
stalks. In particular, polynomial affine-space charts give normal local rings.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory

universe u

/-- The local rings on an affine open with a domain as coordinate ring are domains. -/
theorem isDomain_stalk {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] {x : X} (hx : x ∈ U) : IsDomain (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.isDomain_of_atPrime _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal

/-- The local rings on an affine open with an integrally closed domain as coordinate ring
are integrally closed. -/
theorem isIntegrallyClosed_stalk {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] [IsIntegrallyClosed Γ(X, U)] {x : X} (hx : x ∈ U) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- An affine coordinate domain is integrally closed if all of its local rings are. -/
theorem isIntegrallyClosed_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)]
    (h : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.1)) : IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P hP hmax
  obtain ⟨x, hx⟩ := hU.isoSpec.hom.surjective ⟨P, inferInstance⟩
  have hPX : (hU.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hx
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have : IsLocalization P.primeCompl (X.presheaf.stalk x.1) := by
    simpa only [← hPX] using hU.isLocalization_stalk x
  have := h x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl
      (Localization.AtPrime P) (X.presheaf.stalk x.1)).symm.toRingEquiv


end FrobeniusSplitting
