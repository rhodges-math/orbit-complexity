import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Hom

/-!
# Matrix Linear Form Extension

Matrix linear forms extend to arbitrary coefficient algebras by an
explicit polynomial in the entries, naturally under algebra maps. -/

noncomputable section
namespace ReductiveGroups

variable {K m n A C : Type*} [CommRing K]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

/-- Evaluate a scalar matrix linear form over a coefficient algebra,
using its fixed coefficients on matrix units. -/
def matrixLinearFormValue (f : Matrix m n K →ₗ[K] K) (M : Matrix m n A) : A :=
  ∑ i, ∑ j, algebraMap K A (f (Matrix.single i j 1)) * M i j

/-- The equality is

```lean
matrixLinearFormValue f M = f M
```
-/
@[simp] theorem matrixLinearFormValue_self
    (f : Matrix m n K →ₗ[K] K) (M : Matrix m n K) :
    matrixLinearFormValue f M = f M := by
  have hs (i : m) (j : n) : Matrix.single i j (M i j) =
      M i j • Matrix.single i j (1 : K) := by
    ext a b
    simp [Matrix.single]
  calc
    matrixLinearFormValue f M = f (∑ i, ∑ j, Matrix.single i j (M i j)) := by
      simp only [matrixLinearFormValue, Algebra.algebraMap_self, RingHom.id_apply,
        map_sum, hs, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _
    _ = f M := congrArg f (Matrix.sum_sum_single M)

/-- Every specialization of coefficient algebras commutes with evaluation
of the same fixed matrix linear form. -/
theorem matrixLinearFormValue_map
    (f : Matrix m n K →ₗ[K] K) (M : Matrix m n A) (φ : A →ₐ[K] C) :
    φ (matrixLinearFormValue f M) = matrixLinearFormValue f (M.map φ) := by
  simp only [matrixLinearFormValue, map_sum, map_mul, AlgHom.commutes, Matrix.map_apply]

end ReductiveGroups
