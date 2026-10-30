import Batteries.Tactic.Lint
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Units.Defs

/-!
# The unit-parameter rank-one chart identity

The two affine root charts have reciprocal parameters on their overlap. Their rank-one
matrix identity holds over an arbitrary commutative ring with a specified unit parameter.
-/

namespace SchubertGeometry

open scoped Matrix

universe u

/-- The lower unipotent matrix factors into upper, Weyl, diagonal and upper matrices whenever
its parameter is a unit. This identity is valid without a field or reducedness assumption. -/
theorem rootCurve_matrix_overlap {R : Type u} [CommRing R] (t : Rˣ) :
    (!![1, 0; (t : R), 1] : Matrix (Fin 2) (Fin 2) R) =
      !![1, ((t⁻¹ : Rˣ) : R); 0, 1] *
        !![0, -1; 1, 0] *
        !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)] *
        !![1, ((t⁻¹ : Rˣ) : R); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end SchubertGeometry
