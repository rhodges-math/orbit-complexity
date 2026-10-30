import OrbitComplexity.ReductiveGroups.Lie.Exponential.DerivationLocalNilpotence
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix Row Nilpotence

Iteration of the row action on a family of vectors follows ordinary
matrix powers, regardless of linear relations among the vectors. -/

noncomputable section
namespace ReductiveGroups

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/-- The equality is

```lean
(f ^ m) (v i) = ∑ j, (X ^ m) i j • v j
```
-/
theorem end_pow_row_action (f : Module.End K V) (X : Matrix ι ι K) (v : ι → V)
    (h : ∀ i, f (v i) = ∑ j, X i j • v j) (m : ℕ) (i : ι) :
    (f ^ m) (v i) = ∑ j, (X ^ m) i j • v j := by
  induction m generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, h]
    simp only [map_sum, map_smul, ih, Finset.smul_sum, smul_smul]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm

/-- Nilpotence of the coefficient matrix locally kills every vector of a
row-action family, without requiring it to be linearly independent. -/
theorem end_row_locally_nilpotent (f : Module.End K V) (X : Matrix ι ι K)
    (v : ι → V) (h : ∀ i, f (v i) = ∑ j, X i j • v j)
    (hX : IsNilpotent X) (i : ι) : ∃ m : ℕ, (f ^ m) (v i) = 0 := by
  obtain ⟨m, hm⟩ := hX
  refine ⟨m, ?_⟩
  rw [end_pow_row_action f X v h, hm]
  simp

end ReductiveGroups
