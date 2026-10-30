import OrbitComplexity.GroupActions.Rosenlicht.AwayPolynomials
import OrbitComplexity.GroupActions.Rosenlicht.GenericStandardBasis
import OrbitComplexity.GroupActions.Rosenlicht.IdealLocalization
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Spreading a polynomial ideal and its leading generators

A finite ideal and a lifted leading-monomial basis agree over the fraction
field. A further denominator from the original ring makes them agree after
every coefficient extension that inverts it.
-/

open MvPolynomial
open scoped nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w

attribute [local instance] MvPolynomial.algebraMvPolynomial

private lemma polynomial_map_comp {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] {σ : Type*} :
    (MvPolynomial.map (σ := σ) (algebraMap S T)).comp
        (MvPolynomial.map (algebraMap R S)) = MvPolynomial.map (algebraMap R T) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- A finitely generated polynomial ideal has a lifted leading-monomial basis
whose ideal equals the original ideal after inverting a second nonzero base element. -/
theorem exists_away_ideal_generators (R : Type u) [CommRing R] [IsDomain R]
    {σ : Type v} [Finite σ] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) (hI : I.FG) :
    ∃ r : R, ∃ hr : r ≠ 0, ∃ s : Finset (MvPolynomial σ (Localization.Away r)),
      Ideal.map (MvPolynomial.map (fractionAwayMap R (FractionRing R) r hr))
          (Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))) =
        Ideal.map (MvPolynomial.map (algebraMap R (FractionRing R))) I ∧
      (∀ q ∈ s, IsUnit (m.leadingCoeff q)) ∧
      (∀ p ∈ Ideal.span (s : Set (MvPolynomial σ (Localization.Away r))), p ≠ 0 →
        ∃ q ∈ s, m.degree q ≤ m.degree p) ∧
      ∃ b : R, b ≠ 0 ∧ ∀ (C : Type w) [CommRing C] [Algebra R C]
          [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C],
        IsUnit (algebraMap R C b) →
          Ideal.map (MvPolynomial.map (algebraMap R C)) I =
            Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) C))
              (Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))) := by
  classical
  let F := FractionRing R
  obtain ⟨r, hr, s, hs, hu, hd⟩ := exists_away_leading_generators R F m
    (Ideal.map (MvPolynomial.map (algebraMap R F)) I)
  let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
  let : IsScalarTower R (Localization.Away r) F :=
    IsScalarTower.of_algHom (fractionAwayAlgHom R F r hr)
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial σ (Localization.Away r))
        (nonZeroDivisors R)) (MvPolynomial σ F) :=
    fractionAway_polynomialLocalization R F r hr
  let J := Ideal.map (MvPolynomial.map (algebraMap R (Localization.Away r))) I
  let L := Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))
  have hJL : Ideal.map
      (algebraMap (MvPolynomial σ (Localization.Away r)) (MvPolynomial σ F)) J =
      Ideal.map
        (algebraMap (MvPolynomial σ (Localization.Away r)) (MvPolynomial σ F)) L := by
    change Ideal.map (MvPolynomial.map (fractionAwayMap R F r hr)) J =
      Ideal.map (MvPolynomial.map (fractionAwayMap R F r hr)) L
    rw [hs]
    change Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) F))
      (Ideal.map (MvPolynomial.map (algebraMap R (Localization.Away r))) I) = _
    rw [Ideal.map_map, polynomial_map_comp]
  have hJ : J.FG := hI.map _
  have hL : L.FG := Submodule.fg_span s.finite_toSet
  obtain ⟨b, hb, heq⟩ := exists_localization_map_eq (nonZeroDivisors R) J L hJ hL hJL
  refine ⟨r, hr, s, hs, hu, hd, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, ?_⟩
  intro C _ _ _ _ hunit
  have hunit' : IsUnit (algebraMap (MvPolynomial σ (Localization.Away r))
      (MvPolynomial σ C) (algebraMap R (MvPolynomial σ (Localization.Away r)) b)) := by
    convert hunit.map (MvPolynomial.C (σ := σ)) using 1
    rw [IsScalarTower.algebraMap_apply R (Localization.Away r)
      (MvPolynomial σ (Localization.Away r)) b]
    change MvPolynomial.map (algebraMap (Localization.Away r) C)
      (MvPolynomial.C (algebraMap R (Localization.Away r) b)) = _
    rw [MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply]
  have he := heq (MvPolynomial σ C) hunit'
  change Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) C))
      (Ideal.map (MvPolynomial.map (algebraMap R (Localization.Away r))) I) =
    Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) L at he
  rwa [Ideal.map_map, polynomial_map_comp] at he

end

end GroupActions
