import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages

/-!
# ScalarImageModels

Arithmetic coefficient models and compatible chart comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

private theorem tensorImageHom_cancel (e : K ⊗[S] M ≃ₐ[K] A) :
    tensorImageHom ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans e) =
      scalarImageHom (R := R) e := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r m =>
    change e (Algebra.TensorProduct.cancelBaseChange S R K K M
      ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] m))) = e (algebraMap R K r ⊗ₜ[S] m)
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    congr 1
    simp only [Algebra.smul_def, mul_one]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The intrinsic coefficient image recovers the original algebra after extending
its coefficients to the generic coefficient ring. -/
noncomputable def scalarImageModelEquiv (e : K ⊗[S] M ≃ₐ[K] A) :
    K ⊗[R] (scalarImageHom (R := R) e).range ≃ₐ[K] A :=
  let d := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans e
  let u := Subalgebra.equivOfEq _ _ (congrArg AlgHom.range (tensorImageHom_cancel (R := R) e))
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) u.symm).trans
    (tensorImageEquiv d)

/-- The intrinsic-image scalar comparison evaluates a pure tensor by scalar multiplication. -/
theorem scalarImageModelEquiv_tmul (e : K ⊗[S] M ≃ₐ[K] A) (k : K)
    (m : (scalarImageHom (R := R) e).range) :
    scalarImageModelEquiv e (k ⊗ₜ[R] m) = algebraMap K A k * m.val := rfl

end FrobeniusSplitting
