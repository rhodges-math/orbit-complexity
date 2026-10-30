import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Reductive groups with a split maximal torus

A reductive group is described by its coordinate Hopf algebra, a maximal torus,
a Borel subgroup containing that torus, and a splitting of the torus.

## Main definitions

* `ReductiveGroups.ReductiveGroupData`: the coordinate algebra and chosen subgroups.

## Implementation notes

Closed subgroups correspond contravariantly to Hopf ideals. Thus the containment
of the maximal torus in the Borel subgroup is expressed by the reverse ideal inclusion.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., Springer (1991), Chapters III and IV.
-/

namespace ReductiveGroups

universe u

/-- A reductive affine group with a Borel subgroup and a split maximal torus. -/
structure ReductiveGroupData (K : Type u) [Field K] where
  /-- The finite type commutative coordinate Hopf algebra of the group. -/
  coordinateAlgebra : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K
  /-- The finite set of generators of the character lattice of the chosen torus. -/
  torusIndex : Type u
  /-- The torus has finite rank. -/
  finiteIndex : Finite torusIndex
  /-- The defining Hopf ideal of the maximal torus. -/
  torusIdeal : TauCeti.HopfIdeal K coordinateAlgebra
  /-- The defining Hopf ideal of the Borel subgroup. -/
  borelIdeal : TauCeti.HopfIdeal K coordinateAlgebra
  /-- The maximal torus is contained in the Borel subgroup. -/
  borel_le_torus : borelIdeal ≤ torusIdeal
  /-- The torus is maximal. -/
  isMaximalTorus : TauCeti.HopfIdeal.IsMaximalTorus K
    (CommHopfAlgCat.of K coordinateAlgebra) torusIdeal
  /-- The chosen subgroup is Borel. -/
  isBorel : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K coordinateAlgebra) borelIdeal
  /-- Restriction of functions to the chosen split torus. -/
  torusSplit : coordinateAlgebra →ₐc[K] MonoidAlgebra K (Multiplicative (torusIndex →₀ ℤ))
  /-- Restriction to the torus is surjective. -/
  split_surjective : Function.Surjective torusSplit
  /-- The kernel of restriction defines the maximal torus. -/
  split_eq_zero : ∀ a, torusSplit a = 0 ↔ a ∈ torusIdeal.toIdeal
  /-- The affine group is reductive. -/
  reductive : TauCeti.reductiveCommHopfAlgProperty K coordinateAlgebra

end ReductiveGroups
