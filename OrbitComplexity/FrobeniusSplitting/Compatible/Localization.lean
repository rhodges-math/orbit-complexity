import OrbitComplexity.FrobeniusSplitting.Splittings.Localization
import OrbitComplexity.FrobeniusSplitting.Compatible.Ideals
import Mathlib.RingTheory.Localization.Ideal

/-!
# Compatibility of localized ideals

Localization takes an ideal compatible with a Frobenius splitting to an ideal
compatible with the localized splitting. Clearing a denominator reduces the
assertion to compatibility in the original ring.

## Main results

* `FrobeniusSplitting.RingSplitting.IsCompatible.localize`: compatibility is
  preserved by localization.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Section 1.1.
-/

namespace FrobeniusSplitting.RingSplitting

open IsLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {p : ℕ} (M : Submonoid R) [IsLocalization M S]

/-- A compatible ideal remains compatible after localization. -/
theorem IsCompatible.localize {splitting : RingSplitting R p} {ideal : Ideal R}
    (hcompatible : splitting.IsCompatible ideal) (hp : 0 < p) :
    (splitting.localize (S := S) M hp).IsCompatible (ideal.map (algebraMap R S)) := by
  intro x hx
  obtain ⟨⟨⟨a, ha⟩, s⟩, heq⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  have hnum : a * (s : R) ^ (p - 1) ∈ ideal := ideal.mul_mem_right _ ha
  have hpower : algebraMap R S (s : R) ^ p * x =
      algebraMap R S (a * (s : R) ^ (p - 1)) := by
    rw [(algebraMap R S).map_mul, (algebraMap R S).map_pow]
    calc
      algebraMap R S (s : R) ^ p * x =
          (x * algebraMap R S (s : R)) * algebraMap R S (s : R) ^ (p - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
        ring
      _ = algebraMap R S a * algebraMap R S (s : R) ^ (p - 1) := by rw [heq]
  have hsplit := congrArg (splitting.localize (S := S) M hp) hpower
  rw [(splitting.localize (S := S) M hp).map_pow_mul, localize_algebraMap] at hsplit
  apply (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s)).1
  rw [hsplit]
  exact Ideal.mem_map_of_mem _ (hcompatible hnum)

end FrobeniusSplitting.RingSplitting
