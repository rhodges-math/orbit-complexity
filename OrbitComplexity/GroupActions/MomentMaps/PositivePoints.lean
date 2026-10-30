import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Ring
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
import Batteries.Tactic.Lint

/-! # Positive characters of a lattice

A real additive functional gives a positive complex character, whose value
is the real exponential of half that functional. These characters provide
the positive points for finite-dimensional torus actions.
-/

set_option autoImplicit false

noncomputable section

namespace GroupActions

variable {M : Type*} [AddCommGroup M]

/-- The positive complex character associated to half a real additive functional. -/
def positiveCharacter (f : M →+ ℝ) : Multiplicative M →* ℂˣ :=
  Complex.expMonoidHom.toHomUnits.comp
    (AddMonoidHom.toMultiplicative
      (Complex.ofRealHom.toAddMonoidHom.comp ((1 / 2 : ℝ) • f)))

/-- A positive character has the expected positive real value. -/
theorem positiveCharacter_apply (f : M →+ ℝ) (m : M) :
    (positiveCharacter f (Multiplicative.ofAdd m) : ℂ) =
      (Real.exp (f m / 2) : ℂ) := by
  change Complex.exp (((1 / 2 : ℝ) * f m : ℝ) : ℂ) = _
  rw [show (1 / 2 : ℝ) * f m = f m / 2 by ring]
  exact (Complex.ofReal_exp (f m / 2)).symm


end GroupActions
