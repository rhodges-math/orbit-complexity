import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Gauss
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import Mathlib.Algebra.Polynomial.Roots

/-! # Exact regular simple-frame restrictions, including the zero parameter -/

open ReductiveGroups TauCeti GroupActions

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def simplePolynomial (i : G.rootBase.support) : Polynomial K :=
  gaPolynomialEquiv K (G.simpleRootMap i
    (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
      (positiveDetCoefficient G)))

private theorem simplePolynomial_eval (i : G.rootBase.support) (t : K) :
    (simplePolynomial G i).eval t =
      (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹).ofConv
        (positiveDetCoefficient G) := by
  rw [simplePolynomial, gaPolynomialEquiv_eval_point]
  change (gaParameterPoint (G.simpleRootMap i) t).ofConv
    (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
      (positiveDetCoefficient G)) = _
  exact HopfAlgebra.ofConv_rightTranslationAlgHom _ _ _

/-- The pullback of the determinant coefficient to the positive frame is X squared. -/
theorem positiveDet_simple_polynomial (i : G.rootBase.support) :
    gaPolynomialEquiv K (G.simpleRootMap i
      (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
        (positiveDetCoefficient G))) = Polynomial.X ^ 2 := by
  change simplePolynomial G i = Polynomial.X ^ 2
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun n : ℕ => ((n + 1 : ℕ) : K))) :=
    Set.infinite_range_of_injective (by
      intro m n h
      exact Nat.add_right_cancel (Nat.cast_injective h))
  apply hinf.mono
  rintro t ⟨n, rfl⟩
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  change (simplePolynomial G i).eval ((n + 1 : ℕ) : K) =
    (Polynomial.X ^ 2).eval ((n + 1 : ℕ) : K)
  rw [simplePolynomial_eval]
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Units.val_mk0] using
    positiveDet_simpleGauss_unit G i (Units.mk0 (((n + 1 : ℕ) : K)) hn)

/-- The positive simple frame has exact coefficient t squared also at t=0. -/
theorem positiveDet_simple_frame (i : G.rootBase.support) (t : K) :
    (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹).ofConv
      (positiveDetCoefficient G) = t ^ 2 := by
  have h := congrArg (Polynomial.eval t) (positiveDet_simple_polynomial G i)
  change (simplePolynomial G i).eval t = (Polynomial.X ^ 2).eval t at h
  rw [simplePolynomial_eval, Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h

/-- The pullback to the negative simple-root frame is the constant function one. -/
theorem positiveDet_negative_polynomial (i : G.rootBase.support) :
    G.negativeSimpleRootMap i (positiveDetCoefficient G) = 1 := by
  apply (gaPolynomialEquiv K).injective
  apply Polynomial.funext
  intro t
  rw [map_one, Polynomial.eval_one, gaPolynomialEquiv_eval_point]
  change (gaParameterPoint (G.negativeSimpleRootMap i) t).ofConv
    (positiveDetCoefficient G) = 1
  exact positiveDet_negative_simple G i t

end SchubertGeometry.DeterminantSection
