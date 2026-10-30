import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # Rank-three Deodhar coordinates

The two distinguished subexpressions of the word s₁s₂s₁ for the identity give the
following products of root elements and simple representatives.

## Main results

* `deodhar_product_decreasing`: the product for the subexpression s₁1s₁.
* `deodhar_product_positive`: the product for the positive subexpression 111.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  Example 3.18.
-/

namespace SchubertOrbits

variable {K : Type*} [CommRing K]

/-- The root-element product for the subexpression s₁1s₁ of s₁s₂s₁. -/
theorem deodhar_product_decreasing (parameter coordinate : K) :
    (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 1, 0; 0, parameter, 1] *
      (!![1, coordinate, 0; 0, 1, 0; 0, 0, 1] * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) =
        !![1, 0, 0; -coordinate, 1, 0; -parameter, 0, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The root-element product for the positive subexpression 111 of s₁s₂s₁. -/
theorem deodhar_product_positive (first second third : K) :
    (!![1, 0, 0; first, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 1, 0; 0, second, 1] * !![1, 0, 0; third, 1, 0; 0, 0, 1] =
        !![1, 0, 0; first + third, 1, 0; second * third, second, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

end SchubertOrbits
