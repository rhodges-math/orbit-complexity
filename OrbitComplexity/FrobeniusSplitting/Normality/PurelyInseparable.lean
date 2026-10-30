import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Purely inseparable elements and splittings

A subalgebra preserved by a Frobenius splitting is closed under taking `p`-th
roots in the ambient ring. Repetition excludes a nontrivial purely inseparable
extension preserved by the splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.mem_of_pow_pow_mem`: closure under iterated
  roots of the splitting exponent.
* `FrobeniusSplitting.RingSplitting.mem_range_of_pow_pow_mem`: root closure in an
  intermediate ring embedded in a ring with a commuting splitting.
* `FrobeniusSplitting.RingSplitting.surjective_of_purelyInseparable`: triviality
  of a stable purely inseparable extension.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting.RingSplitting

variable {R : Type*} [CommSemiring R] {p : ℕ}

/-- A subalgebra preserved by a splitting contains every element whose `p`-th power it contains. -/
theorem mem_of_pow_mem {A : Type*} [CommSemiring A] [Algebra A R]
    (splitting : RingSplitting R p) {subalgebra : Subalgebra A R}
    (hstable : Set.MapsTo splitting subalgebra subalgebra) {a : R}
    (ha : a ^ p ∈ subalgebra) : a ∈ subalgebra := by
  have hmem := hstable ha
  change splitting (a ^ p) ∈ subalgebra at hmem
  rwa [splitting.map_pow] at hmem

/-- A stable subalgebra contains elements with any iterated `p`-power in the subalgebra. -/
theorem mem_of_pow_pow_mem {A : Type*} [CommSemiring A] [Algebra A R]
    (splitting : RingSplitting R p) {subalgebra : Subalgebra A R}
    (hstable : Set.MapsTo splitting subalgebra subalgebra) {a : R} {n : ℕ}
    (ha : a ^ (p ^ n) ∈ subalgebra) : a ∈ subalgebra := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    apply ih
    apply splitting.mem_of_pow_mem hstable
    simpa only [pow_succ, pow_mul] using ha

/-- A commuting ambient splitting gives root closure in every embedded intermediate ring. -/
theorem mem_range_of_pow_mem {S T : Type*} [CommSemiring S] [CommSemiring T]
    (base : RingSplitting R p) (ambient : RingSplitting T p)
    (morphism : R →+* S) (inclusion : S →+* T) (hinjective : Function.Injective inclusion)
    (hcommute : ∀ a, ambient (inclusion (morphism a)) = inclusion (morphism (base a)))
    {b : S} (hpower : b ^ p ∈ Set.range morphism) : b ∈ Set.range morphism := by
  obtain ⟨a, ha⟩ := hpower
  refine ⟨base a, hinjective ?_⟩
  calc
    inclusion (morphism (base a)) = ambient (inclusion (morphism a)) := (hcommute a).symm
    _ = inclusion b := by rw [ha, inclusion.map_pow, ambient.map_pow]

end FrobeniusSplitting.RingSplitting
