import OrbitComplexity.FrobeniusSplitting.Compatible.Quotient
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Compatible irreducible components

Every minimal prime over a compatible ideal is compatible. The proof first treats
a minimal prime of a reduced split ring by localizing, then passes to the quotient
by the compatible ideal.

## Main results

* `FrobeniusSplitting.RingSplitting.compatible_minimalPrime`: compatibility of a
  minimal prime of a split ring.
* `FrobeniusSplitting.RingSplitting.IsCompatible.minimalPrime`: compatibility of
  every irreducible component of a compatible closed subscheme in the affine case.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.1.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommRing R] {p : ℕ}

/-- Every minimal prime of a split ring is compatible with the splitting. -/
theorem compatible_minimalPrime (splitting : RingSplitting R p) (hp : 1 < p)
    {prime : Ideal R} (hprime : prime ∈ minimalPrimes R) :
    splitting.IsCompatible prime := by
  have := splitting.isReduced hp
  have := hprime.isPrime
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime prime) prime (⊥ : Ideal R) hprime
  rw [Ideal.map_bot, Ideal.radical_bot_of_isReduced] at hrad
  intro a ha
  have hlocal := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime prime)) ha
  rw [← hrad, Ideal.mem_bot] at hlocal
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff prime.primeCompl (Localization.AtPrime prime) a).1 hlocal
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans hp))
  have hpower : (s : R) ^ (n + 1) * a = 0 := by
    rw [pow_succ, mul_assoc, hs, mul_zero]
  have hsplit : (s : R) * splitting a = 0 := by
    rw [← splitting.map_pow_mul, hpower, splitting.map_zero]
  have hmem : (s : R) * splitting a ∈ prime := hsplit.symm ▸ prime.zero_mem
  exact (hprime.isPrime.mem_or_mem hmem).resolve_left s.property

/-- Every minimal prime above a compatible ideal is compatible with the splitting. -/
theorem IsCompatible.minimalPrime {splitting : RingSplitting R p} {ideal prime : Ideal R}
    (hcompatible : splitting.IsCompatible ideal) (hp : 1 < p)
    (hprime : prime ∈ ideal.minimalPrimes) : splitting.IsCompatible prime := by
  rw [Ideal.minimalPrimes_eq_comap] at hprime
  obtain ⟨prime, hprime, rfl⟩ := hprime
  intro a ha
  change Ideal.Quotient.mk ideal (splitting a) ∈ prime
  rw [← splitting.quotient_mk ideal hcompatible a]
  exact compatible_minimalPrime (splitting.quotient ideal hcompatible) hp hprime ha

end FrobeniusSplitting.RingSplitting
