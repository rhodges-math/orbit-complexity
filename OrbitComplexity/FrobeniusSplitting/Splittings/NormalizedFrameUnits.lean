import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialFrameUnits
import Batteries.Tactic.Lint

/-!
# Normalized sections and polynomial coframes

A normalized prior operator provides both reducedness of the coefficient
ring and regularity of the top coefficient. These identify the whole section
equation after an affine change of polynomial coordinates.
-/

noncomputable section

universe u

open Polynomial

namespace FrobeniusSplitting

/-- Prior normalization and a section comparison determine the full polynomial equation. -/
theorem polynomialCoframe_section_eq {R : Type u} [CommRing R]
    {p : ℕ} (phi : FrobeniusLinearMap R p) (hp : 1 < p)
    (P Q : Polynomial R) (n : ℕ) (hQ : Q.natDegree ≤ n)
    (a delta : Rˣ) (b : R) (u : (Polynomial R)ˣ)
    (hsection : P = (u : Polynomial R) * Q.comp (C (a : R) * X + C b))
    (hcoeff : P.coeff n = (delta : R) * Q.coeff n)
    (hnormalized : phi (Q.coeff n) = 1) :
    P = C ((delta : R) * (↑(a⁻¹) : R) ^ n) * Q.comp (C (a : R) * X + C b) := by
  let : IsReduced R := (phi.toSplitting (Q.coeff n) hnormalized).isReduced hp
  have hu := polynomialFrameUnit_of_normalized phi (lt_trans Nat.zero_lt_one hp)
    P Q n hQ a delta b u hsection hcoeff hnormalized
  exact hsection.trans (congrArg (fun f : Polynomial R =>
    f * Q.comp (C (a : R) * X + C b)) hu)

end FrobeniusSplitting
