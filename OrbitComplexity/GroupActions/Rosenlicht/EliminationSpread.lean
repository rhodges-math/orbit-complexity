import OrbitComplexity.GroupActions.Rosenlicht.EliminationKernels
import OrbitComplexity.GroupActions.Rosenlicht.IdealSpread
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Submodule

/-!
# Uniform specialization of elimination kernels

A finite ideal and a lifted lexicographic leading basis agree after inverting
one further denominator. Flat extension to the fraction field compares their
elimination kernels, and finite generation spreads this equality. Thus one
nonzero base element excludes every new relation under specialization.
-/

open MvPolynomial
open scoped nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w

attribute [local instance] MvPolynomial.algebraMvPolynomial

private lemma elimination_map_comp {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] {σ : Type*} :
    (MvPolynomial.map (σ := σ) (algebraMap S T)).comp
        (MvPolynomial.map (algebraMap R S)) = MvPolynomial.map (algebraMap R T) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- A finite-type polynomial elimination kernel specializes after inverting
two nonzero base elements. -/
theorem exists_away_elimination_kernel (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {σ : Type v} [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ R)) (t : Set σ) (ht : IsUpperSet t) :
    ∃ r : R, r ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧
      ∀ (C : Type w) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C]
          [IsScalarTower R (Localization.Away r) C], IsUnit (algebraMap R C b) →
        RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R C))) t) =
          (RingHom.ker (quotientVariableMap I t)).map
            (MvPolynomial.map (algebraMap R C)) := by
  classical
  obtain ⟨r, hr, s, hs, hu, hd, b₁, hb₁, heq⟩ :=
    exists_away_ideal_generators R MonomialOrder.lex I I.fg_of_isNoetherianRing
  let F := FractionRing R
  let : Algebra (Localization.Away r) F := (fractionAwayAlgHom R F r hr).toAlgebra
  let : IsScalarTower R (Localization.Away r) F :=
    IsScalarTower.of_algHom (fractionAwayAlgHom R F r hr)
  let : IsFractionRing (Localization.Away r) F := fractionAway_isFractionRing R F r hr
  let : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  let : Module.Flat (Localization.Away r) F :=
    IsLocalization.flat F (nonZeroDivisors (Localization.Away r))
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial t (Localization.Away r))
        (nonZeroDivisors R)) (MvPolynomial t F) :=
    fractionAway_polynomialLocalization R F r hr
  let L := Ideal.span (s : Set (MvPolynomial σ (Localization.Away r)))
  let P := (RingHom.ker (quotientVariableMap I t)).map
    (MvPolynomial.map (algebraMap R (Localization.Away r)))
  let Q := RingHom.ker (quotientVariableMap L t)
  change L.map (MvPolynomial.map (algebraMap (Localization.Away r) F)) =
    I.map (MvPolynomial.map (algebraMap R F)) at hs
  have hPQ : P.map
      (algebraMap (MvPolynomial t (Localization.Away r)) (MvPolynomial t F)) =
      Q.map (algebraMap (MvPolynomial t (Localization.Away r)) (MvPolynomial t F)) := by
    change Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) F))
        ((RingHom.ker (quotientVariableMap I t)).map
          (MvPolynomial.map (algebraMap R (Localization.Away r)))) =
      Q.map (MvPolynomial.map (algebraMap (Localization.Away r) F))
    rw [Ideal.map_map, elimination_map_comp,
      ← ker_quotientVariableMap_of_flat F I t,
      ← ker_quotientVariableMap_of_flat F L t, hs]
  obtain ⟨b₂, hb₂, heq₂⟩ := exists_localization_map_eq (nonZeroDivisors R) P Q
    P.fg_of_isNoetherianRing Q.fg_of_isNoetherianRing hPQ
  refine ⟨r, hr, b₁ * b₂, mul_ne_zero hb₁ (mem_nonZeroDivisors_iff_ne_zero.mp hb₂), ?_⟩
  intro C _ _ _ _ hunit
  have hu' : IsUnit (algebraMap R C b₁) ∧ IsUnit (algebraMap R C b₂) := by
    apply IsUnit.mul_iff.mp
    simpa only [map_mul] using hunit
  have hunit₂ : IsUnit (algebraMap (MvPolynomial t (Localization.Away r))
      (MvPolynomial t C) (algebraMap R (MvPolynomial t (Localization.Away r)) b₂)) := by
    convert hu'.2.map (MvPolynomial.C (σ := t)) using 1
    rw [IsScalarTower.algebraMap_apply R (Localization.Away r)
      (MvPolynomial t (Localization.Away r)) b₂]
    change MvPolynomial.map (algebraMap (Localization.Away r) C)
      (MvPolynomial.C (algebraMap R (Localization.Away r) b₂)) = _
    rw [MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply]
  have hPQ' := heq₂ (MvPolynomial t C) hunit₂
  change P.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) =
    Q.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) at hPQ'
  have hL : I.map (MvPolynomial.map (algebraMap R C)) =
      L.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) := heq C hu'.1
  calc
    RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R C))) t) =
        RingHom.ker (quotientVariableMap
          (L.map (MvPolynomial.map (algebraMap (Localization.Away r) C))) t) :=
      congrArg (fun J ↦ RingHom.ker (quotientVariableMap J t)) hL
    _ = Q.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) :=
      ker_quotientVariableMap_baseChange C s hu hd t ht
    _ = P.map (MvPolynomial.map (algebraMap (Localization.Away r) C)) := hPQ'.symm
    _ = (RingHom.ker (quotientVariableMap I t)).map
        (MvPolynomial.map (algebraMap R C)) := by
      change Ideal.map (MvPolynomial.map (algebraMap (Localization.Away r) C))
        ((RingHom.ker (quotientVariableMap I t)).map
          (MvPolynomial.map (algebraMap R (Localization.Away r)))) = _
      rw [Ideal.map_map, elimination_map_comp]

/-- Inverting one nonzero base element makes the full elimination relation
ideal commute with every coefficient extension. -/
theorem exists_elimination_baseChange (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {σ : Type v} [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ R)) (t : Set σ) (ht : IsUpperSet t) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type w) [CommRing C] [Algebra R C],
      IsUnit (algebraMap R C d) →
        RingHom.ker (quotientVariableMap (I.map (MvPolynomial.map (algebraMap R C))) t) =
          (RingHom.ker (quotientVariableMap I t)).map
            (MvPolynomial.map (algebraMap R C)) := by
  obtain ⟨r, hr, b, hb, heq⟩ := exists_away_elimination_kernel R I t ht
  refine ⟨r * b, mul_ne_zero hr hb, ?_⟩
  intro C _ _ hunit
  have hu : IsUnit (algebraMap R C r) ∧ IsUnit (algebraMap R C b) := by
    apply IsUnit.mul_iff.mp
    simpa only [map_mul] using hunit
  let j : Localization.Away r →ₐ[R] C :=
    { __ := Localization.awayLift (algebraMap R C) r hu.1
      commutes' := by
        intro a
        change (Localization.awayLift (algebraMap R C) r hu.1)
          (algebraMap R (Localization.Away r) a) = _
        exact IsLocalization.Away.lift_eq r hu.1 a }
  let : Algebra (Localization.Away r) C := j.toAlgebra
  let : IsScalarTower R (Localization.Away r) C := IsScalarTower.of_algHom j
  exact heq C hu.2

end

end GroupActions
