import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Finite tests for fraction values

Finitely many fractions have one common nonzero denominator. Where that denominator is
invertible, equality of their coordinate values forces equality of the prescribed values.
-/

open scoped BigOperators

namespace GroupActions

noncomputable section

universe u v w z

/-- Finitely many fractions in an embedded ring are distinguished by the
numerator and denominator coordinates away from one nonzero denominator. -/
theorem exists_fraction_value_tests (R : Type u) [CommRing R]
    (F : Type v) [Field F] (A : Type w) [CommRing A]
    (j : R →+* F) (hj : Function.Injective j) (φ : A →+* F) (ψ : A →+* R)
    (hψ : j.comp ψ = φ) (S : Finset R)
    (hS : ∀ a ∈ S, ∃ n b : A, φ b ≠ 0 ∧ j a = φ n / φ b) :
    ∃ d : R, d ≠ 0 ∧ ∀ (C : Type z) [CommRing C] (f g : R →+* C),
      IsUnit (f d) → f.comp ψ = g.comp ψ → ∀ a ∈ S, f a = g a := by
  classical
  choose n b hb he using fun a : S ↦ hS a.val a.property
  let d : R := ∏ a : S, ψ (b a)
  have hd : d ≠ 0 := by
    intro hz
    have hprod : (∏ a : S, φ (b a)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun a _ ↦ hb a)
    apply hprod
    have hjd : j d = ∏ a : S, φ (b a) := by
      simp only [d, map_prod]
      exact Finset.prod_congr rfl (fun a _ ↦ congrArg (fun h : A →+* F ↦ h (b a)) hψ)
    rw [← hjd, hz, map_zero]
  refine ⟨d, hd, ?_⟩
  intro C _ f g hfd hfg a ha
  let i : S := ⟨a, ha⟩
  have hunit : IsUnit (f (ψ (b i))) := by
    have hp : IsUnit (∏ a : S, f (ψ (b a))) := by
      simpa only [d, map_prod] using hfd
    exact IsUnit.prod_univ_iff.mp hp i
  have hmul : a * ψ (b i) = ψ (n i) := by
    apply hj
    rw [map_mul]
    have hb' : j (ψ (b i)) = φ (b i) := congrArg (fun h : A →+* F ↦ h (b i)) hψ
    have hn' : j (ψ (n i)) = φ (n i) := congrArg (fun h : A →+* F ↦ h (n i)) hψ
    rw [hb', hn', he i]
    exact div_mul_cancel₀ _ (hb i)
  have heq (c : A) : f (ψ c) = g (ψ c) :=
    congrArg (fun h : A →+* C ↦ h c) hfg
  apply hunit.mul_right_cancel
  calc
    f a * f (ψ (b i)) = f (ψ (n i)) := by rw [← map_mul, hmul]
    _ = g (ψ (n i)) := heq _
    _ = g a * g (ψ (b i)) := by rw [← map_mul, hmul]
    _ = g a * f (ψ (b i)) := by rw [heq]

end

end GroupActions
