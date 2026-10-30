import OrbitComplexity.GroupActions.Tori.LaurentDimension
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Dimension of lattice group algebras

A finite free character lattice has a basis. The resulting group algebra is a split torus
coordinate ring, whose dimension is the integral rank of the lattice.

## Main results

* `GroupActions.ringKrullDim_lattice`: a lattice group algebra has the lattice rank as dimension.
-/

namespace GroupActions

noncomputable section

universe u

/-- The group algebra of a finite free integral module has dimension equal to its rank. -/
theorem ringKrullDim_lattice (K : Type u) [Field K] (M : Type u)
    [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M] :
    ringKrullDim (MonoidAlgebra K (Multiplicative M)) =
      (Module.finrank ℤ M : WithBot ℕ∞) := by
  let b := Module.Free.chooseBasis ℤ M
  let : Finite (Module.Free.ChooseBasisIndex ℤ M) := Module.Finite.finite_basis b
  let : Fintype (Module.Free.ChooseBasisIndex ℤ M) := Fintype.ofFinite _
  let e := MonoidAlgebra.domCongr K K b.repr.toAddEquiv.toMultiplicative
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ringKrullDim_splitTorus,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_basis b]

end

end GroupActions
