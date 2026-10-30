import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedRootSquares
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.LinearMap
import Lean.Elab.Tactic.Omega
import Batteries.Tactic.Lint

/-! # Splitting the retained root-chart divisor

At an odd exponent, the retained square contributes the factor of degree
p - 1 required for compatibility with the root-coordinate ideal.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry ReductiveGroups GroupActions TauCeti FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

private theorem weightedSpan {R : Type*} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (a w : R)
    (hn : φ (w * a ^ (p - 1)) = 1) :
    (φ.toSplitting (w * a ^ (p - 1)) hn).IsCompatible (Ideal.span {a}) := by
  let ψ := φ.weight w
  have hψ : ψ (a ^ (p - 1)) = 1 := hn
  have h := ψ.toSplitting_compatible_span hp a hψ
  have he : ψ.toSplitting (a ^ (p - 1)) hψ =
      φ.toSplitting (w * a ^ (p - 1)) hn := by
    apply RingSplitting.ext
    intro x
    change φ (w * (a ^ (p - 1) * x)) = φ ((w * a ^ (p - 1)) * x)
    rw [mul_assoc]
  exact he ▸ h

private theorem squareWeight {R : Type*} [CommRing R] {p : ℕ}
    (hp : Odd p) (a w : R) :
    (w * a ^ 2) ^ ((p - 1) / 2) =
      w ^ ((p - 1) / 2) * a ^ (p - 1) := by
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  rw [mul_pow, ← pow_mul, hhalf]

end SchubertGeometry.DeterminantSection
