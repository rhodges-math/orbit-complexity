import OrbitComplexity.GroupActions.Rosenlicht.IdealLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ordinary points of polynomial relation ideals
-/

open MvPolynomial
open scoped nonZeroDivisors

namespace GroupActions

noncomputable section

universe u v w

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Generic generators of a polynomial ideal test its vanishing at every
ordinary point after one nonzero coefficient denominator is inverted. -/
theorem exists_relation_vanishing
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (m : ℕ) (I : Ideal (MvPolynomial (Fin m) R))
    (s : Finset (MvPolynomial (Fin m) R))
    (hs : I.map (MvPolynomial.map (algebraMap R F)) =
      (Ideal.span (s : Set (MvPolynomial (Fin m) R))).map
        (MvPolynomial.map (algebraMap R F))) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type w) [CommRing C] (x : R →+* C),
      IsUnit (x d) → ∀ y : Fin m → C,
        (∀ p ∈ I, MvPolynomial.eval₂Hom x y p = 0) ↔
          ∀ p ∈ s, MvPolynomial.eval₂Hom x y p = 0 := by
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin m) R) (nonZeroDivisors R))
      (MvPolynomial (Fin m) F) := by
    change IsLocalization ((nonZeroDivisors R).map (MvPolynomial.C (σ := Fin m)))
      (MvPolynomial (Fin m) F)
    infer_instance
  obtain ⟨d, hd, hmap⟩ := exists_localization_map_eq (nonZeroDivisors R) I
    (Ideal.span (s : Set (MvPolynomial (Fin m) R)))
    I.fg_of_isNoetherianRing (Ideal.span _).fg_of_isNoetherianRing hs
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
  intro C _ x hx y
  let ev := MvPolynomial.eval₂Hom x y
  let : Algebra (MvPolynomial (Fin m) R) C := ev.toAlgebra
  have hu : IsUnit (algebraMap (MvPolynomial (Fin m) R) C
      (algebraMap R (MvPolynomial (Fin m) R) d)) := by
    change IsUnit (ev (MvPolynomial.C d))
    simpa only [ev, MvPolynomial.eval₂Hom_C] using hx
  have heq := hmap C hu
  change I.map ev = (Ideal.span (s : Set (MvPolynomial (Fin m) R))).map ev at heq
  have hiff : (∀ p ∈ I, ev p = 0) ↔
      ∀ p ∈ Ideal.span (s : Set (MvPolynomial (Fin m) R)), ev p = 0 := by
    change I ≤ RingHom.ker ev ↔ Ideal.span (s : Set (MvPolynomial (Fin m) R)) ≤ RingHom.ker ev
    rw [← Ideal.map_eq_bot_iff_le_ker, ← Ideal.map_eq_bot_iff_le_ker, heq]
  change (∀ p ∈ I, ev p = 0) ↔ ∀ p ∈ s, ev p = 0
  rw [hiff]
  change Ideal.span (s : Set (MvPolynomial (Fin m) R)) ≤ RingHom.ker ev ↔ _
  exact Ideal.span_le

end

end GroupActions
