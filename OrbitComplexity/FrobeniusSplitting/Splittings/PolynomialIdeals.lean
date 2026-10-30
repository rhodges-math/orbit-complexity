import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import OrbitComplexity.FrobeniusSplitting.Splittings.LinearMap
import Mathlib.RingTheory.Polynomial.Basic
import Batteries.Tactic.Lint

/-! # Extended ideals under weighted polynomial trace -/

set_option autoImplicit false
namespace FrobeniusSplitting

variable {K A : Type*} {p : ℕ} [Field K] [ExpChar K p] [PerfectRing K p]
variable [CommRing A] [Algebra K A]

private theorem trace_preserves_map (ψ : FrobeniusLinearMap A p) (I : Ideal A)
    (hψ : ∀ a ∈ I, ψ a ∈ I) (P f : Polynomial A)
    (hf : f ∈ I.map Polynomial.C) :
    (polynomialTraceOfOperator (K := K) ψ).weight P f ∈ I.map Polynomial.C := by
  apply Ideal.mem_map_C_iff.mpr
  intro n
  rw [FrobeniusLinearMap.weight_apply, polynomialTraceOfOperator_coeff]
  exact hψ _ (Ideal.mem_map_C_iff.mp
    ((I.map Polynomial.C).mul_mem_left P hf) (p * n + (p - 1)))

/-- A normalized weighted polynomial trace preserves every ideal extended from a
coefficient ideal that its base operator preserves. -/
theorem polynomialTrace_compatible_map (ψ : FrobeniusLinearMap A p) (I : Ideal A)
    (hψ : ∀ a ∈ I, ψ a ∈ I) (P : Polynomial A)
    (hP : (polynomialTraceOfOperator (K := K) ψ).weight P 1 = 1) :
    (((polynomialTraceOfOperator (K := K) ψ).weight P).toSplitting 1 hP).IsCompatible
      (I.map Polynomial.C) := by
  intro f hf
  rw [FrobeniusLinearMap.toSplitting_apply, one_mul]
  exact trace_preserves_map ψ I hψ P f hf

end FrobeniusSplitting
