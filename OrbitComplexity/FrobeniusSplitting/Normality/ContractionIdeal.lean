import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Defs

/-!
# Polynomial kernel vanishing from a punctured contraction

A polynomial vanishing after the natural map to Laurent polynomials is already
zero over an arbitrary coefficient ring. This applies to the kernel of a
surjective coordinate map without reducedness or domain assumptions.

The localization variant proves the same implication through an arbitrary
localization at regular elements. Fractions are represented only by
IsLocalization.mk', so the proof never computes with a concrete localization.

The geometric punctured-map factorization supplying the Laurent equation
belongs to the consuming cell-contraction module.
-/

namespace FrobeniusSplitting

universe u v w

/-- A punctured polynomial contraction preserves a coordinate kernel if its
Laurent extension vanishes on that kernel. No surjectivity or reducedness is
needed for this implication. -/
theorem kernel_polynomial_vanish
    {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (q : A →+* C) (α : A →+* Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q (α f)) = 0) :
    ∀ f : A, q f = 0 → Polynomial.map q (α f) = 0 := by
  intro f hf
  exact Polynomial.toLaurent_eq_zero.mp (hLaurent f hf)

/-- The kernel inclusion needed to descend a polynomial contraction through
the specified coordinate quotient. -/
theorem kernel_polynomial_le
    {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (q : A →+* C) (α : A →+* Polynomial A)
    (hLaurent : ∀ f : A, q f = 0 →
      Polynomial.toLaurent (Polynomial.map q (α f)) = 0) :
    RingHom.ker q ≤ RingHom.ker ((Polynomial.mapRingHom q).comp α) := by
  intro f hf
  exact RingHom.mem_ker.mpr
    (kernel_polynomial_vanish q α hLaurent f (RingHom.mem_ker.mp hf))

end FrobeniusSplitting
