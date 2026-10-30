import OrbitComplexity.ReductiveGroups.Geometry.PositiveWeightTriangularity
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Diagonal Polynomial Weights

A diagonal-equivariant polynomial has only monomials carrying its
specified diagonal character. -/

noncomputable section
namespace ReductiveGroups

open MvPolynomial

variable {κ K : Type*} [Fintype κ] [Field K]

omit [Fintype κ] in
private theorem aeval_diagonal_monomial
    (c : κ → K) (m : κ →₀ ℕ) (r : K) :
    aeval (fun j : κ => C (c j) * X j) (monomial m r) =
      monomial m (r * m.prod (fun j e => c j ^ e)) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, ← map_pow, Finsupp.prod]
  rw [Finset.prod_mul_distrib]
  simp only [map_prod, map_mul, MvPolynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  ring

/-- Diagonal substitution scales each coefficient by the character of its
monomial. -/
theorem coeff_aeval_diagonal
    (c : κ → K) (p : MvPolynomial κ K) (m : κ →₀ ℕ) :
    (aeval (fun j : κ => C (c j) * X j) p).coeff m =
      p.coeff m * m.prod (fun j e => c j ^ e) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum, aeval_diagonal_monomial, coeff_monomial]
  by_cases hm : m ∈ p.support
  · simp [hm]
  · simp [hm, notMem_support_iff.mp hm]

/-- Every supported monomial of a diagonal-equivariant polynomial carries
the stated diagonal character. Equality is assumed only on field-valued
evaluations; infinitude of the field recovers the polynomial identity. -/
theorem DiagonalPolynomialWeights.character_of_diagonal_equivariant
    [Infinite K]
    {T : Type*} (p : MvPolynomial κ K)
    (c : κ → T → K) (β : T → K)
    (h : ∀ t (a : κ → K),
      eval (fun j => c j t * a j) p = β t * eval a p)
    (m : κ →₀ ℕ) (hm : m ∈ p.support) (t : T) :
    m.prod (fun j e => c j t ^ e) = β t := by
  let D : MvPolynomial κ K :=
    aeval (fun j => C (c j t) * X j) p
  have hpoly : D = C (β t) * p := by
    apply MvPolynomial.funext
    intro a
    change aeval a (aeval (fun j => C (c j t) * X j) p) =
      aeval a (C (β t) * p)
    rw [comp_aeval_apply]
    simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
    simpa only [aeval_eq_eval] using h t a
  have hcoeff := congrArg (fun r : MvPolynomial κ K => r.coeff m) hpoly
  rw [coeff_aeval_diagonal, coeff_C_mul] at hcoeff
  have hnz : p.coeff m ≠ 0 := mem_support_iff.mp hm
  apply mul_left_cancel₀ hnz
  simpa only [mul_comm] using hcoeff

end ReductiveGroups
