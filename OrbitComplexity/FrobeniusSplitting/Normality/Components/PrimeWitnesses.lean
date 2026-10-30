import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Batteries.Tactic.Lint

/-! # Equational witnesses for a minimal prime

Localization at a minimal prime gives a power-membership equation for
each of its generators, with a multiplier outside the prime. Such equations
also certify minimality after a scalar extension that preserves the
multiplier's nonvanishing.
-/

set_option autoImplicit false

namespace FrobeniusSplitting

/-- Every element of a minimal prime has a power lying in the original ideal
after multiplication by an element outside that prime. -/
theorem exists_mul_pow_mem_minimalPrime {R : Type*} [CommRing R]
    {I P : Ideal R} (hminimal : P ∈ I.minimalPrimes) {x : R} (hx : x ∈ P) :
    ∃ s : R, s ∉ P ∧ ∃ n : ℕ, s * x ^ n ∈ I := by
  classical
  let : P.IsPrime := hminimal.isPrime
  let A := Localization.AtPrime P
  have heq := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := A) P I hminimal
  have hx' : algebraMap R A x ∈ (I.map (algebraMap R A)).radical := by
    rw [heq]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨n, hn⟩ := hx'
  have hn' : algebraMap R A (x ^ n) ∈ I.map (algebraMap R A) := by
    rw [map_pow]
    exact hn
  obtain ⟨s, hs, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (M := P.primeCompl) (S := A) I (x ^ n)).mp hn'
  exact ⟨s, hs, n, hmem⟩

/-- Power-membership equations on generators certify that a prime is minimal
over an ideal, provided their multipliers remain outside the prime. -/
theorem mem_minimalPrimes_of_generators {R : Type*} [CommRing R]
    (I P : Ideal R) (hprime : P.IsPrime) (G : Set R)
    (hspan : Ideal.span G = P) (hle : I ≤ P)
    (hwitness : ∀ x ∈ G, ∃ s : R, s ∉ P ∧ ∃ n : ℕ, s * x ^ n ∈ I) :
    P ∈ I.minimalPrimes := by
  refine ⟨⟨hprime, hle⟩, ?_⟩
  intro Q hQ hQP
  rw [← hspan]
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨s, hs, n, hmem⟩ := hwitness x hx
  have hsQ : s ∉ Q := fun h => hs (hQP h)
  have hpow : x ^ n ∈ Q := (hQ.1.mem_or_mem (hQ.2 hmem)).resolve_left hsQ
  exact hQ.1.mem_of_pow_mem n hpow

end FrobeniusSplitting
