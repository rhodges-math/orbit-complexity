import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix Basis Conjugation

Change of basis as conjugation by an invertible matrix. -/

noncomputable section
namespace ReductiveGroups
open Module

variable {K : Type*} [Field K] (n : ℕ)

/-- Every basis change on `Fin n → K` is conjugation by a GL matrix.
The formula includes the empty basis when `n = 0`. -/
theorem exists_matrixBasisConjugation
    (b : Basis (Fin n) K (Fin n → K)) :
    ∃ P : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ X : Matrix (Fin n) (Fin n) K,
        (P : Matrix (Fin n) (Fin n) K) * X * (↑P⁻¹ : Matrix (Fin n) (Fin n) K) =
          LinearMap.toMatrix b b (Matrix.toLin' X) := by
  classical
  let e := b.equivFun
  let P₀ : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' e.toLinearMap
  let Q₀ : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' e.symm.toLinearMap
  have hPQ : P₀ * Q₀ = 1 := by
    calc
      P₀ * Q₀ = LinearMap.toMatrix' (e.toLinearMap * e.symm.toLinearMap) := by
        rw [LinearMap.toMatrix'_mul]
      _ = 1 := by
        have he : e.toLinearMap * e.symm.toLinearMap = 1 := by
          apply LinearMap.ext
          intro v
          change e (e.symm v) = v
          exact e.apply_symm_apply v
        rw [he, LinearMap.toMatrix'_one]
  have hQP : Q₀ * P₀ = 1 := by
    calc
      Q₀ * P₀ = LinearMap.toMatrix' (e.symm.toLinearMap * e.toLinearMap) := by
        rw [LinearMap.toMatrix'_mul]
      _ = 1 := by
        have he : e.symm.toLinearMap * e.toLinearMap = 1 := by
          apply LinearMap.ext
          intro v
          change e.symm (e v) = v
          exact e.symm_apply_apply v
        rw [he, LinearMap.toMatrix'_one]
  let P : Matrix.GeneralLinearGroup (Fin n) K := ⟨P₀, Q₀, hPQ, hQP⟩
  refine ⟨P, ?_⟩
  intro X
  change P₀ * X * Q₀ = LinearMap.toMatrix b b (Matrix.toLin' X)
  change P₀ * X * Q₀ =
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ Matrix.toLin' X ∘ₗ e.symm.toLinearMap)
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
  simp only [P₀, Q₀, LinearMap.toMatrix'_toLin', mul_assoc]

end ReductiveGroups
