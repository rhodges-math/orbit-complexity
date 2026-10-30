import OrbitComplexity.FrobeniusSplitting.Normality.PurelyInseparable
import OrbitComplexity.FrobeniusSplitting.Normality.UniversallyInjective
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Root closure modulo an ideal in the base

An ideal in an intermediate ring may be contained in the image of the base ring
without the intermediate ring itself admitting a splitting. A commuting splitting
on an ambient ring nevertheless gives root closure after passing to the quotient
by such an ideal.

## Main results

* `FrobeniusSplitting.RingSplitting.quotient_mem_range_of_pow`: root closure in the
  quotient of an intermediate ring.
* `FrobeniusSplitting.RingSplitting.quotient_mem_range_of_pow_pow`: closure under
  every iterated splitting exponent.
* `FrobeniusSplitting.RingSplitting.quotient_surjective_of_specMap`: surjectivity
  when the quotient rings are fields and the spectrum map is universally injective.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting.RingSplitting

open AlgebraicGeometry CategoryTheory

universe u

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {p : ℕ}

/-- Root closure passes to a quotient by an ideal contained in the image of the base. -/
theorem quotient_mem_range_of_pow (base : RingSplitting R p) (ambient : RingSplitting T p)
    (morphism : R →+* S) (inclusion : S →+* T) (hinjective : Function.Injective inclusion)
    (hcommute : ∀ a, ambient (inclusion (morphism a)) = inclusion (morphism (base a)))
    (ideal : Ideal S) (hideal : (ideal : Set S) ⊆ Set.range morphism)
    {b : S ⧸ ideal}
    (hpower : b ^ p ∈ Set.range (Ideal.quotientMap ideal morphism le_rfl)) :
    b ∈ Set.range (Ideal.quotientMap ideal morphism le_rfl) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := hpower
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk, ← (Ideal.Quotient.mk ideal).map_pow,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨c, hc⟩ := hideal ha
  have hbase : b ^ p ∈ Set.range morphism := by
    refine ⟨a - c, ?_⟩
    rw [morphism.map_sub, hc]
    ring
  obtain ⟨d, hd⟩ := base.mem_range_of_pow_mem ambient morphism inclusion hinjective hcommute hbase
  refine ⟨Ideal.Quotient.mk (ideal.comap morphism) d, ?_⟩
  rw [Ideal.quotientMap_mk, hd]

/-- Root closure modulo an ideal in the base holds for every iterated splitting exponent. -/
theorem quotient_mem_range_of_pow_pow (base : RingSplitting R p) (ambient : RingSplitting T p)
    (morphism : R →+* S) (inclusion : S →+* T) (hinjective : Function.Injective inclusion)
    (hcommute : ∀ a, ambient (inclusion (morphism a)) = inclusion (morphism (base a)))
    (ideal : Ideal S) (hideal : (ideal : Set S) ⊆ Set.range morphism)
    {b : S ⧸ ideal} {n : ℕ}
    (hpower : b ^ (p ^ n) ∈ Set.range (Ideal.quotientMap ideal morphism le_rfl)) :
    b ∈ Set.range (Ideal.quotientMap ideal morphism le_rfl) := by
  induction n with
  | zero => simpa using hpower
  | succ n ih =>
    apply ih
    apply base.quotient_mem_range_of_pow ambient morphism inclusion hinjective hcommute ideal hideal
    simpa only [pow_succ, pow_mul] using hpower

/-- A universally injective field quotient of an embedded split base has a surjective base map. -/
theorem quotient_surjective_of_specMap {A B : Type u} {K : Type*}
    [CommRing A] [CommRing B] [CommRing K] {q : ℕ}
    (base : RingSplitting A q) (ambient : RingSplitting K q)
    (morphism : A →+* B) (inclusion : B →+* K) (hinjective : Function.Injective inclusion)
    (hcommute : ∀ a, ambient (inclusion (morphism a)) = inclusion (morphism (base a)))
    (ideal : Ideal B) (hideal : (ideal : Set B) ⊆ Set.range morphism)
    (hsource : IsField (A ⧸ ideal.comap morphism)) (htarget : IsField (B ⧸ ideal))
    [ExpChar (A ⧸ ideal.comap morphism) q]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap ideal morphism le_rfl)))] :
    Function.Surjective (Ideal.quotientMap ideal morphism le_rfl) := by
  let := hsource.toField
  let := htarget.toField
  let : Algebra (A ⧸ ideal.comap morphism) (B ⧸ ideal) :=
    (Ideal.quotientMap ideal morphism le_rfl).toAlgebra
  have : IsPurelyInseparable (A ⧸ ideal.comap morphism) (B ⧸ ideal) :=
    FrobeniusSplitting.purelyInseparable_of_specMap
  intro b
  obtain ⟨n, hpower⟩ := IsPurelyInseparable.pow_mem (A ⧸ ideal.comap morphism) q b
  exact base.quotient_mem_range_of_pow_pow ambient morphism inclusion hinjective hcommute
    ideal hideal hpower

end FrobeniusSplitting.RingSplitting
