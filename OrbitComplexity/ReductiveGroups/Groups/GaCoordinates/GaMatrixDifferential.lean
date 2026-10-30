import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixPolynomial
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentCoordinate
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent

/-!
# Ga Matrix Differential

Additive-group matrix morphisms are exponentials of their
tangent maps at the identity. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)

/-- The linear coefficient of the pulled-back generic matrix is the matrix
of the differential applied to the unit tangent of the additive group. -/
theorem GaMatrixPolynomial.coeff_one_differential
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) :
    (gaMatrixPolynomial n φ).coeff 1 =
      TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K) φ (gaOriginDerivation K)) := by
  ext i j
  simp only [gaMatrixPolynomial, matPolyEquiv_coeff_apply, Matrix.map_apply,
    TauCeti.GeneralLinear.tangentMatrix_apply, gaOriginDerivation_comp_apply,
    TauCeti.GeneralLinear.genericMatrix_apply]

variable [CharZero K]

/-- The differential of an additive-group morphism into GL is a
nilpotent matrix.  -/
theorem gaMatrix_differential_nilpotent
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) :
    IsNilpotent (TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K) φ (gaOriginDerivation K))) := by
  rw [← GaMatrixPolynomial.coeff_one_differential]
  apply PolynomialOneParameterExponential.one_parameter_linear_nilpotent
  · rw [gaMatrixPolynomial_eval_points]
    simp
  · intro t s
    simp only [gaMatrixPolynomial_eval_points]
    simp

/-- The matrix of every point on the original additive-group morphism is
the finite exponential of the parameter times its differential. -/
theorem GaMatrixPoints.eq_exponential_differential
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) (t : K) :
    (gaMatrixPoints n φ (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K) (t • TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K) φ (gaOriginDerivation K))) := by
  rw [gaMatrixPoints_eq_exponential, GaMatrixPolynomial.coeff_one_differential]

/-- Retain an intermediate affine group through its coordinate algebra:
first differentiate its additive subgroup, then its matrix representation.
The original intermediate group is not replaced by the matrix group. -/
theorem RepresentedGaPoints.eq_exponential_differential
    {B : Type*} [CommRing B] [Bialgebra K B]
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) (t : K) :
    (gaMatrixPoints n (x.comp ρ) (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K) (t • TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K) ρ
          (TauCeti.derivationComp (B := K) x (gaOriginDerivation K)))) := by
  rw [GaMatrixPoints.eq_exponential_differential, TauCeti.derivationComp_comp,
    LinearMap.comp_apply]

end ReductiveGroups
