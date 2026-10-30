import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local rings inside reduced Artinian rings

A local subring integrally closed in a reduced Artinian ring is a domain.
Indeed, integral closedness lifts the idempotents that distinguish the Artinian
ring's field factors, whereas a local ring has only the idempotents zero and one.
-/

namespace FrobeniusSplitting

open Polynomial

variable {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]

private theorem idempotent_integral {t : T} (ht : t * t = t) : IsIntegral A t := by
  refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), ?_⟩
  simpa [pow_two] using sub_eq_zero.mpr ht

private theorem local_idempotent [IsLocalRing A] {a : A} (ha : a * a = a) :
    a = 0 ∨ a = 1 := by
  have h : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hunit | hunit
  · exact Or.inr (sub_eq_zero.mp ((hunit.mul_right_eq_zero).mp h)).symm
  · exact Or.inl ((hunit.mul_left_eq_zero).mp h)

/-- A local subring integrally closed in a reduced Artinian ring is a domain. -/
theorem isDomain_of_artinian_extension [IsLocalRing A] [IsIntegrallyClosedIn A T]
    [IsArtinianRing T] [IsReduced T] : IsDomain A := by
  classical
  have hinj := (isIntegrallyClosedIn_iff (R := A) (A := T)).mp inferInstance |>.1
  have : Nontrivial T := ⟨⟨0, 1, fun h ↦ zero_ne_one (hinj (by simpa using h))⟩⟩
  let e := IsArtinianRing.equivPi T
  have : Subsingleton (MaximalSpectrum T) := by
    refine ⟨fun m n ↦ ?_⟩
    by_contra hmn
    let t : T := e.symm (Pi.single m 1)
    have ht : t * t = t := by
      apply e.injective
      ext i
      by_cases h : i = m
      · subst i
        simp [t]
      · simp [t, h]
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral
      (idempotent_integral (A := A) ht)
    have haa : a * a = a := hinj (by rw [map_mul, ha, ht])
    rcases local_idempotent haa with h | h
    · have ht0 : t = 0 := by simpa [h] using ha.symm
      have hm := congrArg (fun z ↦ e z m) ht0
      simp [t] at hm
    · have ht1 : t = 1 := by simpa [h] using ha.symm
      have hn := congrArg (fun z ↦ e z n) ht1
      simp [t, Ne.symm hmn] at hn
  have : IsLocalRing T := IsLocalRing.of_singleton_maximalSpectrum
  let := (IsArtinianRing.isField_of_isReduced_of_isLocalRing T).toField
  exact hinj.isDomain _

end FrobeniusSplitting
