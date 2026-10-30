import OrbitComplexity.FrobeniusSplitting.Compatible.Local
import OrbitComplexity.FrobeniusSplitting.Compatible.Components
import Batteries.Tactic.Lint

/-! # Compatible irreducible components on schemes

Affine minimal primes transfer compatibility to an irreducible component.
The corresponding induction starts with the ambient scheme and divisors,
then takes components of intersections of previously split closed subschemes.
-/

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace FrobeniusSplitting.SchemeSplitting

/-- A closed subscheme whose affine ideals are minimal primes of a compatible
ideal is compatibly split. An affine open disjoint from it has the unit ideal. -/
theorem IsCompatible.minimalPrime {X : Scheme.{u}} {p : ℕ} {κ : Type v}
    {splitting : SchemeSplitting X p} {ideal component : X.IdealSheafData}
    (hideal : splitting.IsCompatible ideal) (hp : 1 < p)
    (U : κ → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hcomponent : ∀ i,
      component.ideal (U i) = ⊤ ∨
        component.ideal (U i) ∈ (ideal.ideal (U i)).minimalPrimes) :
    splitting.IsCompatible component := by
  refine isCompatible_of_cover splitting component (by omega) U hU ?_
  intro i
  rcases hcomponent i with hunit | hprime
  · rw [hunit]
    exact RingSplitting.compatible_top (splitting.onOpen (U i))
  · exact RingSplitting.IsCompatible.minimalPrime (hideal (U i)) hp hprime

/-- A family of closed subschemes is compatibly split if its members of rank
at most one are split and every higher member is an affine minimal-prime
component of an intersection of two members of smaller rank. -/
theorem isCompatible_induction {X : Scheme.{u}} {p : ℕ} {κ : Type v} {ι : Type w}
    (splitting : SchemeSplitting X p) (hp : 1 < p)
    (U : κ → X.affineOpens) (hU : ⨆ j, (U j).1 = ⊤)
    (ideal : ι → X.IdealSheafData) (rank : ι → ℕ)
    (hbase : ∀ i, rank i ≤ 1 → splitting.IsCompatible (ideal i))
    (hstep : ∀ i, 1 < rank i →
      ∃ a b, rank a < rank i ∧ rank b < rank i ∧
        ∀ j, (ideal i).ideal (U j) = ⊤ ∨
          (ideal i).ideal (U j) ∈ ((ideal a ⊔ ideal b).ideal (U j)).minimalPrimes) :
    ∀ i, splitting.IsCompatible (ideal i) := by
  suffices h : ∀ n, ∀ i, rank i = n → splitting.IsCompatible (ideal i) by
    intro i
    exact h (rank i) i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    by_cases hlow : rank i ≤ 1
    · exact hbase i hlow
    obtain ⟨a, b, ha, hb, hcomponent⟩ := hstep i (lt_of_not_ge hlow)
    have ha' : rank a < n := by omega
    have hb' : rank b < n := by omega
    have hleft := ih (rank a) ha' a rfl
    have hright := ih (rank b) hb' b rfl
    exact (hleft.sup hright).minimalPrime hp U hU hcomponent

end FrobeniusSplitting.SchemeSplitting
