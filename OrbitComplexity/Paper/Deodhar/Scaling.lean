import OrbitComplexity.Paper.Deodhar.Matrices
import Mathlib.Tactic.FieldSimp

/-! # Diagonal scaling of rank-three Deodhar coordinates

Left multiplication by a diagonal matrix scales the root parameters by quotients of its
diagonal entries, and leaves a diagonal matrix on the right.

## Main results

* `deodhar_scaling_decreasing`: scaling for the subexpression s₁1s₁.
* `deodhar_scaling_positive`: scaling for the positive subexpression 111.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson Varieties*,
  Example 3.18.
-/

namespace SchubertOrbits

variable {K : Type*} [Field K]

/-- Diagonal multiplication scales the two coordinates of the subexpression s₁1s₁. -/
theorem deodhar_scaling_decreasing (first second third parameter coordinate : K)
    (hfirst : first ≠ 0) :
    (!![first, 0, 0; 0, second, 0; 0, 0, third] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; -coordinate, 1, 0; -parameter, 0, 1] =
        !![1, 0, 0; -(second / first * coordinate), 1, 0;
          -(third / first * parameter), 0, 1] *
          !![first, 0, 0; 0, second, 0; 0, 0, third] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp

/-- Diagonal multiplication scales all three coordinates of the positive subexpression. -/
theorem deodhar_scaling_positive (first second third left middle right : K)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    (!![first, 0, 0; 0, second, 0; 0, 0, third] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; left + right, 1, 0; middle * right, middle, 1] =
        !![1, 0, 0; second / first * left + second / first * right, 1, 0;
          (third / second * middle) * (second / first * right),
          third / second * middle, 1] *
          !![first, 0, 0; 0, second, 0; 0, 0, third] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp

end SchubertOrbits
