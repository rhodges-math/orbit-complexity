import OrbitComplexity.FrobeniusSplitting.Normality.Etale
import OrbitComplexity.FrobeniusSplitting.Normality.Stalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Normal local rings over normal bases

Integral polynomial coefficients give integral closedness of multivariate
polynomial rings over normal domains. Standard étale coordinates then prove
normality of smooth local algebras over such domains. Affine localization gives
the corresponding assertion for smooth morphisms to integral normal schemes.

## Main results

* `FrobeniusSplitting.isIntegrallyClosed_mvPolynomial`: polynomial normality.
* `FrobeniusSplitting.localRings_of_smooth_base`: normality of smooth local algebras.
* `FrobeniusSplitting.stalks_of_smooth_base`: normality under smooth morphisms.
-/

namespace FrobeniusSplitting

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Polynomial rings in any set of variables over normal domains are integrally closed. -/
theorem isIntegrallyClosed_mvPolynomial {R σ : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (MvPolynomial σ R) := by
  let K := FractionRing R
  have : IsIntegrallyClosed (MvPolynomial σ K) := inferInstance
  suffices IsIntegrallyClosedIn (MvPolynomial σ R) (MvPolynomial σ K) from
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _ (MvPolynomial σ K)
  apply isIntegrallyClosedIn_iff.mpr
  constructor
  · exact MvPolynomial.map_injective (f := algebraMap R K) (IsFractionRing.injective R K)
  · intro f hf
    change f ∈ Set.range (MvPolynomial.map (algebraMap R K))
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro r hr
    obtain ⟨d, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hr
    exact IsIntegrallyClosed.algebraMap_eq_of_integral
      ((MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hf) d)

/-- Local rings of smooth algebras over normal domains are normal domains. -/
theorem localRings_of_smooth_base {R S B : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] [CommRing B] [IsLocalRing B]
    [Algebra S B] (P : Ideal S) [P.IsPrime] [IsLocalization P.primeCompl B] :
    IsDomain B ∧ IsIntegrallyClosed B := by
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := P)
  let A := MvPolynomial (Fin n) R
  have : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial
  let Sf := Localization.Away f
  let : Algebra A Sf := hAlg
  have : IsScalarTower R A Sf := hTower
  have : Algebra.IsStandardEtale A Sf := hEtale
  have hle : Submonoid.powers f ≤ P.primeCompl :=
    Submonoid.powers_le.mpr hf
  let : Algebra Sf B := IsLocalization.localizationAlgebraOfSubmonoidLe
    Sf B (Submonoid.powers f) P.primeCompl hle
  have : IsScalarTower S Sf B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      Sf B (Submonoid.powers f) P.primeCompl hle
  let : Algebra A B := ((algebraMap Sf B).comp (algebraMap A Sf)).toAlgebra
  have : IsScalarTower A Sf B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (P.primeCompl.map (algebraMap S Sf)) B :=
    IsLocalization.isLocalization_of_submonoid_le Sf B
      (Submonoid.powers f) P.primeCompl hle
  exact ⟨isDomain_of_etale_local (R := A) (P.primeCompl.map (algebraMap S Sf)),
    isIntegrallyClosed_of_etale_loc (R := A) (P.primeCompl.map (algebraMap S Sf))⟩

open AlgebraicGeometry CategoryTheory

universe u

end FrobeniusSplitting
