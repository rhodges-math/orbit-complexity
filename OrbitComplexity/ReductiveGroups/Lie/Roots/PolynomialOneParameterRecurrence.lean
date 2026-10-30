import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Polynomial One Parameter Recurrence

Coefficients of polynomial one-parameter matrix groups. -/

noncomputable section
namespace ReductiveGroups
open Polynomial

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]

private def entryPoly (p : Polynomial (Matrix ι ι K)) (i j : ι) : Polynomial K :=
  matPolyEquiv.symm p i j

omit [CharZero K] in
private theorem entryPoly_coeff (p : Polynomial (Matrix ι ι K)) (i j : ι) (n : ℕ) :
    (entryPoly p i j).coeff n = (p.coeff n) i j := by
  simp [entryPoly]

omit [CharZero K] in
private theorem entryPoly_eval (p : Polynomial (Matrix ι ι K)) (i j : ι) (t : K) :
    (entryPoly p i j).eval t =
      (p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) t)) i j := by
  have hscalar : algebraMap K (Matrix ι ι K) t = Matrix.scalar ι t := by
    ext a b
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [hscalar]
  simpa only [entryPoly, Polynomial.eval₂_id, Matrix.map_apply] using
    congrArg (fun M : Matrix ι ι K => M i j) (matPolyEquiv_symm_map_eval p t)

/-- The additive-parameter group law forces the ordinary exponential
coefficient recurrence, in matrix multiplication order. -/
theorem PolynomialOneParameterRecurrence.one_parameter_coeff_recurrence
    (p : Polynomial (Matrix ι ι K))
    (hadd : ∀ t s : K,
      p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) (t + s)) =
        p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) t) *
          p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) s))
    (n : ℕ) :
    (n + 1 : K) • p.coeff (n + 1) = p.coeff n * p.coeff 1 := by
  let P (t : K) : Matrix ι ι K :=
    p.eval₂ (RingHom.id _) (algebraMap K (Matrix ι ι K) t)
  let q (i j : ι) : Polynomial K := entryPoly p i j
  have hp (i j : ι) (t : K) : (q i j).eval t = P t i j :=
    entryPoly_eval p i j t
  have hshift (t : K) (i j : ι) :
      Polynomial.taylor t (q i j) =
        ∑ a : ι, Polynomial.C (P t i a) * q a j := by
    apply Polynomial.funext
    intro s
    calc
      (Polynomial.taylor t (q i j)).eval s = P (s + t) i j := by
        rw [Polynomial.taylor_eval, hp]
      _ = (P t * P s) i j := by
        rw [add_comm]
        exact congrArg (fun M : Matrix ι ι K => M i j) (hadd t s)
      _ = ∑ a : ι, P t i a * (q a j).eval s := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun a _ => by rw [hp])
      _ = (∑ a : ι, Polynomial.C (P t i a) * q a j).eval s := by
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_C_mul]
  have hfirst (t : K) (i j : ι) :
      (q i j).derivative.eval t = (P t * p.coeff 1) i j := by
    have h := congrArg (fun z : Polynomial K => z.coeff 1) (hshift t i j)
    simpa [Polynomial.coeff_C_mul,
      Matrix.mul_apply, q, entryPoly_coeff] using h
  have hderiv (i j : ι) :
      (q i j).derivative =
        ∑ a : ι, q i a * Polynomial.C ((p.coeff 1) a j) := by
    apply Polynomial.funext
    intro t
    calc
      (q i j).derivative.eval t = (P t * p.coeff 1) i j := hfirst t i j
      _ = ∑ a : ι, (q i a).eval t * (p.coeff 1) a j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun a _ => by rw [hp])
      _ = (∑ a : ι, q i a * Polynomial.C ((p.coeff 1) a j)).eval t := by
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  ext i j
  have h := congrArg (fun z : Polynomial K => z.coeff n) (hderiv i j)
  simpa [Polynomial.coeff_derivative,
    Polynomial.coeff_mul_C, Matrix.mul_apply, q, entryPoly_coeff,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using h

end ReductiveGroups
