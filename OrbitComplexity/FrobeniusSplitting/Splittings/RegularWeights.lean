import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import Mathlib.Algebra.Ring.Regular
import Batteries.Tactic.Lint

/-! # Cancellation of regular weights in Frobenius-linear operators

An element on which a Frobenius-linear operator takes the value one is
regular. Multiplying the input by a regular element is injective on the
space of Frobenius-linear operators.
-/

namespace FrobeniusSplitting.FrobeniusLinearMap

variable {R : Type*} [CommRing R] {p : ℕ}

/-- A normalized argument of a positive-power Frobenius-linear operator is regular. -/
theorem isRegular_of_normalized (φ : FrobeniusLinearMap R p) (hp : 0 < p)
    (c : R) (h : φ c = 1) : IsRegular c := by
  have hleft : IsLeftRegular c := by
    apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
    intro b hcb
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    have hb : b ^ (q + 1) * c = 0 := by
      calc
        b ^ (q + 1) * c = b ^ q * (c * b) := by rw [pow_succ]; ac_rfl
        _ = 0 := by rw [hcb, mul_zero]
    have he := φ.map_pow_mul b c
    rw [hb, φ.map_zero, h, mul_one] at he
    exact he.symm
  refine ⟨hleft, ?_⟩
  intro a b hab
  apply hleft
  calc
    c * a = a * c := mul_comm _ _
    _ = b * c := hab
    _ = c * b := mul_comm _ _

/-- A regular input weight can be cancelled from equality of Frobenius-linear operators. -/
theorem weight_injective (hp : 0 < p) (c : R) (hc : IsRegular c) :
    Function.Injective (fun φ : FrobeniusLinearMap R p ↦ φ.weight c) := by
  intro φ ψ h
  apply FrobeniusLinearMap.ext
  intro x
  apply hc.left
  have he := congrArg (fun θ : FrobeniusLinearMap R p ↦ θ (c ^ (p - 1) * x)) h
  have hpow : c * c ^ (p - 1) = c ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rw [weight_apply, weight_apply, ← mul_assoc, hpow,
    φ.map_pow_mul, ψ.map_pow_mul] at he
  exact he

end FrobeniusSplitting.FrobeniusLinearMap
