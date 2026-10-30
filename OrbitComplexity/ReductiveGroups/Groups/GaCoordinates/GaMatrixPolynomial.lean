import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate
import OrbitComplexity.ReductiveGroups.Lie.Exponential.PolynomialOneParameterExponential
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Ga Matrix Polynomial

Additive-group morphisms into GL have polynomial matrix coordinates. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] [CharZero K] (n : ℕ)

/-- The generic GL matrix after pullback along a morphism from the
additive-group coordinate Hopf algebra, expressed as a matrix polynomial. -/
def gaMatrixPolynomial
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) : Polynomial (Matrix (Fin n) (Fin n) K) :=
  matPolyEquiv
    ((TauCeti.GeneralLinear.genericMatrix K n).map
      (fun a => gaPolynomialEquiv K (φ a)))

/-- The group homomorphism on points induced by `φ`. -/
def gaMatrixPoints
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) :
    Multiplicative K →* (Matrix (Fin n) (Fin n) K)ˣ :=
  ((TauCeti.GeneralLinear.pointsMulEquiv (R := K) (A := K) n).toMonoidHom.comp
    (TauCeti.AlgHom.mapDomain φ)).comp
      (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm.toMonoidHom

omit [CharZero K] in
/-- Scalar evaluation of the pulled-back generic matrix is exactly the
matrix of the point induced by the original Hopf-algebra morphism. -/
theorem gaMatrixPolynomial_eval_points
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) (t : K) :
    polynomialMatrixValue (gaMatrixPolynomial n φ) t =
      (gaMatrixPoints n φ (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) := by
  let q := (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)
  have hscalar : algebraMap K (Matrix (Fin n) (Fin n) K) t =
      Matrix.scalar (Fin n) t := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hpoly : polynomialMatrixValue (gaMatrixPolynomial n φ) t =
      (TauCeti.GeneralLinear.genericMatrix K n).map
        (fun a => q.ofConv (φ a)) := by
    ext i j
    simp only [polynomialMatrixValue, Polynomial.eval₂_id, hscalar,
      gaMatrixPolynomial, matPolyEquiv_eval_eq_map, Matrix.map_apply]
    exact gaPolynomialEquiv_eval_point K t (φ ((TauCeti.GeneralLinear.genericMatrix K n) i j))
  rw [hpoly]
  have hpoint := TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear
    (R := K) n (q.ofConv.comp (φ :
      TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] SymmetricAlgebra K K))
  simpa [gaMatrixPoints, q, Function.comp_def, TauCeti.AlgHom.mapDomain_apply,
    TauCeti.GeneralLinear.pointsMulEquiv_apply] using hpoint

/-- The point homomorphism from `𝔾ₐ` into `GLₙ` is a finite matrix
exponential with generator the linear coefficient of its coordinate polynomial. -/
theorem gaMatrixPoints_eq_exponential
    (φ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      SymmetricAlgebra K K) (t : K) :
    (gaMatrixPoints n φ (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K) (t • (gaMatrixPolynomial n φ).coeff 1) := by
  exact PolynomialOneParameterExponential.unit_one_parameter_eq_exponential
    (gaMatrixPoints n φ) (gaMatrixPolynomial n φ)
    (gaMatrixPolynomial_eval_points n φ) t

end ReductiveGroups
