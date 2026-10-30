import OrbitComplexity.ReductiveGroups.Groups.Additive.UnipotentPointGaIntegration
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentPowerLogarithm

/-!
# Ga Matrix Logarithm

Recover the represented tangent of a Ga morphism from
its matrix at parameter one by a finite logarithmic polynomial. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B]

/-- The matrix of the original tangent of `x` is the linear
coefficient of the finite interpolation of its represented point at `1`.
The nilpotence bound is the only condition. -/
theorem GaAffineGroupTangent.matrix_eq_powerPolynomial_coeff_one
    (n : ℕ) (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (r : ℕ)
    (hpow : ((GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ
        (gaAffineGroupPoints x (Multiplicative.ofAdd 1))) :
          Matrix (Fin n) (Fin n) K) - 1) ^ (r + 1) = 0) :
    affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x) =
      (nilpotentPowerPolynomial (K := K) (r + 1)
        ((GeneralLinear.pointsMulEquiv n
          (AlgHom.mapDomain ρ
            (gaAffineGroupPoints x (Multiplicative.ofAdd 1))) :
              Matrix (Fin n) (Fin n) K) - 1)).coeff 1 := by
  let M : Matrix (Fin n) (Fin n) K :=
    GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ (gaAffineGroupPoints x (Multiplicative.ofAdd 1)))
  let N : Matrix (Fin n) (Fin n) K := M - 1
  have hN : N ^ (r + 1) = 0 := hpow
  let p := nilpotentPowerPolynomial (K := K) (r + 1) N
  have heval (t : K) : polynomialMatrixValue p t =
      nilpotentPowerCurve (K := K) (r + 1) N t :=
    nilpotentPowerPolynomial_eval (K := K) (r + 1) N t
  have hzero : polynomialMatrixValue p 0 = 1 := by
    rw [heval]
    exact nilpotentPowerCurve_zero (r + 1) N (by omega)
  have hadd : ∀ s t : K, polynomialMatrixValue p (s + t) =
      polynomialMatrixValue p s * polynomialMatrixValue p t := by
    intro s t
    simp only [heval]
    exact nilpotentPowerCurve_add (r + 1) N hN s t
  let y := polynomialMatrixGaMorphism p hzero hadd
  have hpoint_y :
      (GeneralLinear.pointsMulEquiv n
        (gaAffineGroupPoints y (Multiplicative.ofAdd 1)) :
          Matrix (Fin n) (Fin n) K) = M := by
    change (gaMatrixPoints n y (Multiplicative.ofAdd 1) :
      Matrix (Fin n) (Fin n) K) = M
    rw [polynomialMatrixGaMorphism_points p hzero hadd 1, heval,
      nilpotentPowerCurve_one (r + 1) N hN]
    dsimp [N]
    abel
  have hpoint_x :
      (GeneralLinear.pointsMulEquiv n
        (gaAffineGroupPoints (x.comp ρ) (Multiplicative.ofAdd 1)) :
          Matrix (Fin n) (Fin n) K) = M := by
    change (gaMatrixPoints n (x.comp ρ) (Multiplicative.ofAdd 1) :
      Matrix (Fin n) (Fin n) K) = M
    rw [← gaAffineGroupPoints_map_matrix n x ρ 1]
  have hyx : y = x.comp ρ := by
    apply gaAffineGroupPoints_one_injective
    apply (GeneralLinear.pointsMulEquiv n).injective
    apply Units.ext
    exact hpoint_y.trans hpoint_x.symm
  have ht := congrArg (fun z : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K =>
      GeneralLinear.tangentMatrix n
        (derivationComp (B := K) z (gaOriginDerivation K))) hyx
  change GeneralLinear.tangentMatrix n
      (derivationComp (B := K)
        (nilpotentMatrixGaMorphism (p.coeff 1)
          (PolynomialOneParameterExponential.one_parameter_linear_nilpotent p hzero hadd))
        (gaOriginDerivation K)) =
    GeneralLinear.tangentMatrix n
      (derivationComp (B := K) (x.comp ρ) (gaOriginDerivation K)) at ht
  rw [nilpotentMatrixGaMorphism_tangent] at ht
  rw [affineGroupMatrixDifferential_apply, gaAffineGroupTangent]
  rw [derivationComp_comp, LinearMap.comp_apply] at ht
  simpa only [p, N, M] using ht.symm

/-- The same tangent matrix is the explicit finite logarithm
of the represented point at parameter one. -/
theorem GaAffineGroupTangent.matrix_eq_finite_logarithm
    (n : ℕ) (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (r : ℕ)
    (hpow : ((GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ
        (gaAffineGroupPoints x (Multiplicative.ofAdd 1))) :
          Matrix (Fin n) (Fin n) K) - 1) ^ (r + 1) = 0) :
    affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x) =
      ∑ k ∈ Finset.range r, ((-1 : K) ^ k / (k + 1 : K)) •
        ((GeneralLinear.pointsMulEquiv n
          (AlgHom.mapDomain ρ
            (gaAffineGroupPoints x (Multiplicative.ofAdd 1))) :
              Matrix (Fin n) (Fin n) K) - 1) ^ (k + 1) := by
  rw [GaAffineGroupTangent.matrix_eq_powerPolynomial_coeff_one n x ρ r hpow]
  exact NilpotentPowerPolynomial.coeff_one_eq_logarithm r _

end ReductiveGroups
