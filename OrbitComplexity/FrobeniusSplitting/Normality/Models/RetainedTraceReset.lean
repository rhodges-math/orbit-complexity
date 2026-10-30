import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # The Cartier trace reset on the retained rightmost chart

P is the unpowered degree-two polynomial retained before any residue prime.
After the chosen coefficient map, the degree p minus one trace coefficient
is its same leading coefficient raised to (p minus one)/2. This scalar remains
INSIDE the arbitrary prior operator. Only the ground field is perfect; the
chart algebra may be nonperfect, nonreduced or the zero ring.
-/

namespace FrobeniusSplitting
noncomputable section
universe u v w

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
  {A : Type v} [CommRing A] [Algebra K A]

private theorem quadratic_power_trace (ψ : FrobeniusLinearMap A p)
    (P : Polynomial A) (hP : P.natDegree ≤ 2) (N : ℕ) (hN : 2 * N = p - 1) :
    polynomialTraceOfOperator (K := K) ψ (P ^ N) =
      Polynomial.C (ψ ((P.coeff 2) ^ N)) := by
  have hi : N * 2 = p - 1 := (Nat.mul_comm N 2).trans hN
  have hp : 0 < p := expChar_pos K p
  apply Polynomial.ext
  intro n
  rw [polynomialTraceOfOperator_coeff]
  cases n with
  | zero =>
    simp only [Nat.mul_zero, zero_add, Polynomial.coeff_C_zero]
    exact congrArg ψ (by
      simpa only [hi] using (Polynomial.coeff_pow_of_natDegree_le (m := N) hP))
  | succ n =>
    have hd := Polynomial.natDegree_pow_le_of_le N hP
    have hm : 0 < p * (n + 1) := Nat.mul_pos hp (Nat.succ_pos n)
    have hgt : (P ^ N).natDegree < p * (n + 1) + (p - 1) := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, map_zero, Polynomial.coeff_C_succ]

/-- The chosen rightmost-chart trace of every retained quadratic power is the
prior operator applied to its leading-coefficient power. The original
model ring and polynomial precede the residue field and its odd characteristic;
no perfectness or characteristic instance is imposed on the chart algebra. -/
theorem retainedFrame_power_trace {B : Type w} [CommRing B]
    (P : Polynomial B) (hP : P.natDegree ≤ 2) (r : B →+* A)
    (ψ : FrobeniusLinearMap A p) (hp : Odd p) :
    polynomialTraceOfOperator (K := K) ψ
        ((Polynomial.map r P) ^ ((p - 1) / 2)) =
      Polynomial.C (ψ ((r (P.coeff 2)) ^ ((p - 1) / 2))) := by
  have hN : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨m, hm⟩ := hp.exists_bit1
    omega
  have hdegree : (Polynomial.map r P).natDegree ≤ 2 :=
    Polynomial.natDegree_map_le.trans hP
  simpa only [Polynomial.coeff_map] using
    quadratic_power_trace (K := K) ψ (Polynomial.map r P) hdegree ((p - 1) / 2) hN

end
end FrobeniusSplitting
