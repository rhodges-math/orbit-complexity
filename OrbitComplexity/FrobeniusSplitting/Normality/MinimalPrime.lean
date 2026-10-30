import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Reduced rings localized at minimal primes

The localization of a reduced ring at a minimal prime is a field: the maximal
ideal is the image of the prime, which is also the nilradical of the localization.

## Main results

* `FrobeniusSplitting.isField_at_minimalPrime`: the field property for an abstract
  localization at a minimal prime.
* `FrobeniusSplitting.isField_quotient_at_minimalPrime`: the corresponding field
  quotient for a radical ideal.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting

/-- Localizing a radical ideal at a minimal prime over it gives a field quotient. -/
theorem isField_quotient_at_minimalPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (ideal prime : Ideal R) [prime.IsPrime]
    [IsLocalization.AtPrime S prime] (hradical : ideal.IsRadical)
    (hprime : prime ∈ ideal.minimalPrimes) :
    IsField (S ⧸ ideal.map (algebraMap R S)) := by
  have := IsLocalization.AtPrime.isLocalRing S prime
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := S) prime ideal hprime
  rw [← IsLocalization.map_radical prime.primeCompl S, hradical.radical] at hrad
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1
  rw [hrad, IsLocalization.AtPrime.map_eq_maximalIdeal prime S]
  infer_instance

end FrobeniusSplitting
