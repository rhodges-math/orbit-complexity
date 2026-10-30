import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialIdeals
import Batteries.Tactic.Lint

/-! # Removing a weight along a prime ideal

A weight outside a prime ideal can be cancelled after Frobenius linearity.
Consequently, compatibility of a weighted splitting implies preservation by
the underlying operator and by its weighted polynomial trace.
-/

set_option autoImplicit false

namespace FrobeniusSplitting

namespace FrobeniusLinearMap

/-- If a weighted operator preserves a prime ideal and its weight is outside
that ideal, then the underlying Frobenius-linear operator preserves it. -/
theorem ideal_of_weight {R : Type*} [CommRing R] {p : ℕ}
    (ψ : FrobeniusLinearMap R p) (I : Ideal R) (hI : I.IsPrime)
    (w : R) (hw : w ∉ I) (hp : 0 < p)
    (hweight : ∀ x ∈ I, ψ (w * x) ∈ I) :
    ∀ x ∈ I, ψ x ∈ I := by
  intro x hx
  have he : w * (w ^ (p - 1) * x) = w ^ p * x := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt hp)]
  have hmul : w * ψ x ∈ I := by
    have h := hweight (w ^ (p - 1) * x) (I.mul_mem_left _ hx)
    rw [he, ψ.map_pow_mul] at h
    exact h
  exact (hI.mem_or_mem hmul).resolve_left hw

end FrobeniusLinearMap

/-- A prime ideal compatible with the weighted coefficient splitting remains
compatible with a normalized polynomial trace when the coefficient weight
is outside that ideal. -/
theorem polynomialTrace_compatible_weight
    {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
    [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (I : Ideal A) (hI : I.IsPrime)
    (w : A) (hw : w ∉ I) (hp : 0 < p) (hnorm : ψ w = 1)
    (hcompatible : (ψ.toSplitting w hnorm).IsCompatible I)
    (P : Polynomial A)
    (hP : (polynomialTraceOfOperator (K := K) ψ).weight P 1 = 1) :
    (((polynomialTraceOfOperator (K := K) ψ).weight P).toSplitting 1 hP).IsCompatible
      (I.map Polynomial.C) := by
  apply polynomialTrace_compatible_map ψ I ?_ P hP
  apply ψ.ideal_of_weight I hI w hw hp
  intro x hx
  simpa only [FrobeniusLinearMap.toSplitting_apply] using hcompatible hx

end FrobeniusSplitting
