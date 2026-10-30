import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Compatibly split ideals

An ideal is compatible with a Frobenius splitting when the splitting preserves it.
Compatible ideals are closed under sums and intersections, and every compatible
ideal of a split ring in positive characteristic is radical.

## Main definitions

* `FrobeniusSplitting.RingSplitting.IsCompatible`: preservation of an ideal.

## Main results

* `FrobeniusSplitting.RingSplitting.IsCompatible.sup`: sums of compatible ideals.
* `FrobeniusSplitting.RingSplitting.IsCompatible.inf`: intersections of compatible ideals.
* `FrobeniusSplitting.RingSplitting.IsCompatible.isRadical`: compatible ideals are radical.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Definition 1.1.3 and
  Proposition 1.2.1.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ}

/-- An ideal is compatible with a splitting if the splitting preserves its elements. -/
def IsCompatible (splitting : RingSplitting R p) (ideal : Ideal R) : Prop :=
  ∀ ⦃a : R⦄, a ∈ ideal → splitting a ∈ ideal

/-- Compatibility means preservation of every element of the ideal. -/
theorem isCompatible_iff (splitting : RingSplitting R p) (ideal : Ideal R) :
    splitting.IsCompatible ideal ↔ ∀ a ∈ ideal, splitting a ∈ ideal :=
  ⟨fun h _ ha ↦ h ha, fun h _ ha ↦ h _ ha⟩

/-- The zero ideal is compatible with every splitting. -/
theorem compatible_bot (splitting : RingSplitting R p) : splitting.IsCompatible ⊥ := by
  intro a ha
  rw [Ideal.mem_bot] at ha
  subst a
  exact splitting.map_zero

/-- The unit ideal is compatible with every splitting. -/
theorem compatible_top (splitting : RingSplitting R p) : splitting.IsCompatible ⊤ :=
  fun _ _ ↦ Submodule.mem_top

variable {splitting : RingSplitting R p} {ideal other : Ideal R}

/-- The intersection of two compatible ideals is compatible with the same splitting. -/
theorem IsCompatible.inf (hideal : splitting.IsCompatible ideal)
    (hother : splitting.IsCompatible other) : splitting.IsCompatible (ideal ⊓ other) :=
  fun _ ha ↦ ⟨hideal ha.1, hother ha.2⟩

/-- The sum of two compatible ideals is compatible with the same splitting. -/
theorem IsCompatible.sup (hideal : splitting.IsCompatible ideal)
    (hother : splitting.IsCompatible other) : splitting.IsCompatible (ideal ⊔ other) := by
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha
  rw [splitting.map_add]
  exact Submodule.add_mem_sup (hideal hb) (hother hc)

/-- An arbitrary intersection of compatible ideals is compatible with the same splitting. -/
theorem IsCompatible.iInf {ι : Sort*} (ideals : ι → Ideal R)
    (hcompatible : ∀ i, splitting.IsCompatible (ideals i)) :
    splitting.IsCompatible (⨅ i, ideals i) := by
  intro a ha
  exact (Submodule.mem_iInf _).2 fun i ↦ hcompatible i ((Submodule.mem_iInf _).1 ha i)

/-- A compatible ideal of a split semiring with exponent greater than one is radical. -/
theorem IsCompatible.isRadical (hideal : splitting.IsCompatible ideal) (hp : 1 < p) :
    ideal.IsRadical := by
  apply (ideal.isRadical_iff_pow_one_lt p hp).2
  intro a ha
  simpa only [splitting.map_pow] using hideal ha

section CommRing

variable {S : Type*} [CommRing S] {splitting : RingSplitting S p}
  {ideal : Ideal S}

/-- The quotient by a compatible ideal of a split ring is reduced. -/
theorem IsCompatible.quotient_isReduced (hideal : splitting.IsCompatible ideal)
    (hp : 1 < p) : IsReduced (S ⧸ ideal) :=
  (Ideal.isRadical_iff_quotient_reduced ideal).1 (hideal.isRadical hp)

end CommRing

end FrobeniusSplitting.RingSplitting
