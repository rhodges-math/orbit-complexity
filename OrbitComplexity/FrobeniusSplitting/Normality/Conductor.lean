import OrbitComplexity.FrobeniusSplitting.Compatible.Ideals
import Mathlib.RingTheory.Conductor

/-!
# Frobenius splittings and conductor ideals

A splitting on an ambient ring that preserves a subalgebra also preserves its
conductor in each intermediate ring. The conductor is radical, and its inverse
image in the base ring is compatible with a commuting splitting.

## Main results

* `FrobeniusSplitting.mapsTo_conductor`: preservation of the conductor image.
* `FrobeniusSplitting.conductor_isRadical`: radicality of the conductor.
* `FrobeniusSplitting.compatible_conductor`: compatibility in the base ring.

## Implementation notes

The conductor of the base ring in an algebra is Mathlib's conductor at one.
Its image in the ambient ring is expressed by `IsLocalization.coeSubmodule`.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting

open IsLocalization

variable {A B K : Type*} [CommRing A] [CommRing B] [CommRing K]
  [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
  [FaithfulSMul B K] {p : ℕ}

/-- A splitting preserving the base algebra also preserves its conductor in an intermediate ring. -/
theorem mapsTo_conductor (splitting : RingSplitting K p)
    (hbase : Set.MapsTo splitting (⊥ : Subalgebra A K) (⊥ : Subalgebra A K)) :
    Set.MapsTo splitting (coeSubmodule K (conductor A (1 : B)))
      (coeSubmodule K (conductor A (1 : B))) := by
  intro a ha
  change a ∈ coeSubmodule K (conductor A (1 : B)) at ha
  change splitting a ∈ coeSubmodule K (conductor A (1 : B))
  rw [mem_coeSubmodule_conductor] at ha ⊢
  simp only [map_one, Algebra.adjoin_singleton_one] at ha ⊢
  intro b
  have hpower : a * algebraMap B K b ^ p ∈ (⊥ : Subalgebra A K) := by
    simpa only [map_pow] using ha (b ^ p)
  have hsplit := hbase hpower
  rwa [mul_comm a, splitting.map_pow_mul, mul_comm] at hsplit

/-- The conductor of a subring preserved by an ambient splitting is radical. -/
theorem conductor_isRadical (splitting : RingSplitting K p)
    (hbase : Set.MapsTo splitting (⊥ : Subalgebra A K) (⊥ : Subalgebra A K))
    (hp : 1 < p) : (conductor A (1 : B)).IsRadical := by
  apply ((conductor A (1 : B)).isRadical_iff_pow_one_lt p hp).2
  intro b hb
  have himage : algebraMap B K b ^ p ∈ coeSubmodule K (conductor A (1 : B)) :=
    ⟨b ^ p, hb, (algebraMap B K).map_pow b p⟩
  have hsplit := mapsTo_conductor splitting hbase himage
  rw [splitting.map_pow] at hsplit
  obtain ⟨c, hc, heq⟩ := hsplit
  have hcb : c = b := FaithfulSMul.algebraMap_injective B K heq
  rwa [hcb] at hc

end FrobeniusSplitting
