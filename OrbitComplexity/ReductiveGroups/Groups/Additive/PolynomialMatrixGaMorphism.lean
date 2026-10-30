import OrbitComplexity.ReductiveGroups.Groups.Additive.NilpotentMatrixGaMorphism
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointDeterminesMorphism

/-!
# Polynomial Matrix Ga Morphism

A polynomial matrix curve with the additive group law gives a
coordinate morphism from Ga. The nilpotent generator is derived from the
polynomial group law, rather than assumed. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Convert a polynomial one-parameter matrix group into its
coordinate bialgebra morphism. -/
def polynomialMatrixGaMorphism (p : Polynomial (Matrix (Fin n) (Fin n) K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ s t : K, polynomialMatrixValue p (s + t) =
      polynomialMatrixValue p s * polynomialMatrixValue p t) :
    GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] SymmetricAlgebra K K :=
  nilpotentMatrixGaMorphism (p.coeff 1)
    (PolynomialOneParameterExponential.one_parameter_linear_nilpotent p hzero hadd)

/-- The constructed coordinate morphism recovers the given matrix curve
at every scalar parameter. -/
theorem polynomialMatrixGaMorphism_points
    (p : Polynomial (Matrix (Fin n) (Fin n) K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ s t : K, polynomialMatrixValue p (s + t) =
      polynomialMatrixValue p s * polynomialMatrixValue p t) (t : K) :
    (gaMatrixPoints n (polynomialMatrixGaMorphism p hzero hadd)
      (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) =
        polynomialMatrixValue p t := by
  rw [polynomialMatrixGaMorphism, nilpotentMatrixGaMorphism_points]
  exact (polynomial_one_parameter_eq_exponential p hzero hadd t).symm

/-- A polynomial matrix one-parameter group through a specified original
GL point integrates uniquely to a Ga morphism through that point. -/
theorem PolynomialMatrixGaMorphism.existsUnique_of_polynomial_matrix_curve
    (p : Polynomial (Matrix (Fin n) (Fin n) K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ s t : K, polynomialMatrixValue p (s + t) =
      polynomialMatrixValue p s * polynomialMatrixValue p t)
    (g : WithConv (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K))
    (hone : polynomialMatrixValue p 1 =
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) K)) :
    ∃! x : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupPoints x (Multiplicative.ofAdd 1) = g := by
  refine ⟨polynomialMatrixGaMorphism p hzero hadd, ?_, ?_⟩
  · apply (GeneralLinear.pointsMulEquiv n).injective
    apply Units.ext
    exact (polynomialMatrixGaMorphism_points p hzero hadd 1).trans hone
  · intro x hx
    apply gaAffineGroupPoints_one_injective
    exact hx.trans (by
      apply (GeneralLinear.pointsMulEquiv n).injective
      apply Units.ext
      exact ((polynomialMatrixGaMorphism_points p hzero hadd 1).trans hone).symm)

end ReductiveGroups
