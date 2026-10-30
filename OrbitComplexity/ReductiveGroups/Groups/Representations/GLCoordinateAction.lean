import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateTruncation
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentOperator
import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentDerivation
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# GL Coordinate Action

The left-invariant tangent operator acts linearly on generic matrix entries. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

variable {K : Type*} [Field K] (n : ℕ)

/-- Left differentiation of a generic matrix entry is multiplication by the tangent matrix
on the row index. -/
theorem leftTangentOperator_genericMatrix_apply
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (i j : Fin n) :
    leftTangentOperator d (TauCeti.GeneralLinear.genericMatrix K n i j) =
      ∑ k : Fin n,
        TauCeti.GeneralLinear.tangentMatrix n d i k •
          TauCeti.GeneralLinear.genericMatrix K n k j := by
  rw [TauCeti.GeneralLinear.genericMatrix_apply]
  unfold leftTangentOperator
  change (TensorProduct.lid K _)
      (TensorProduct.map (scalarTangentLinear d) LinearMap.id
        (Coalgebra.comul (R := K)
          (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
            (TauCeti.GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))))) = _
  rw [TauCeti.GeneralLinear.coordinateHopfAlgebra_comul_X]
  simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    TauCeti.GeneralLinear.genericMatrix_apply, TauCeti.GeneralLinear.tangentMatrix_apply]
  rfl

/-- The generic determinant is group-like in the bundled Hopf algebra. -/
private theorem comul_det_genericMatrix :
    Coalgebra.comul (R := K)
      (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) =
    Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) ⊗ₜ[K]
      Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) := by
  change (Bialgebra.comulAlgHom K
    (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
      (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) = _
  rw [AlgHom.map_det]
  change ((TauCeti.GeneralLinear.genericMatrix K n).map
    (Bialgebra.comulAlgHom K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))).det = _
  rw [TauCeti.GeneralLinear.map_comul_genericMatrix, Matrix.det_mul]
  simp [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

/-- The left tangent operator scales the generic determinant by its tangent value. -/
theorem leftTangentOperator_det_genericMatrix
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K)) :
    leftTangentOperator d
      (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) =
      scalarTangentLinear d
        (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)) •
        Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) := by
  unfold leftTangentOperator
  change (TensorProduct.lid K _)
      (TensorProduct.map (scalarTangentLinear d) LinearMap.id
        (Coalgebra.comul (R := K)
          (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)))) = _
  rw [comul_det_genericMatrix]
  simp

private abbrev detPolynomial : MvPolynomial (Fin n × Fin n) K :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)

/-- The inverse of the determinant, as an element of the coordinate Hopf algebra of `GLₙ`. -/
abbrev detInverseCoordinate : TauCeti.GeneralLinear.coordinateHopfAlgebra K n :=
  TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
    (IsLocalization.Away.invSelf (detPolynomial (K := K) n))

private theorem GLCoordinateAction.genericMatrix_mul_detInverseCoordinate :
    Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) *
      detInverseCoordinate (K := K) n = 1 := by
  have hraw : TauCeti.GeneralLinear.coordinateRingMap K n
      (detPolynomial (K := K) n) *
      IsLocalization.Away.invSelf (detPolynomial (K := K) n) = 1 :=
    IsLocalization.Away.mul_invSelf _
  have hdet : Matrix.det (TauCeti.GeneralLinear.genericMatrix K n) =
      TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
        (TauCeti.GeneralLinear.coordinateRingMap K n
          (detPolynomial (K := K) n)) := by
    rw [← TauCeti.GeneralLinear.det_localizedGenericMatrix]
    change ((TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom.mapMatrix
      (TauCeti.GeneralLinear.localizedGenericMatrix K n)).det =
      TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
        (Matrix.det (TauCeti.GeneralLinear.localizedGenericMatrix K n))
    exact (AlgHom.map_det (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom
      (TauCeti.GeneralLinear.localizedGenericMatrix K n)).symm
  rw [hdet]
  change TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
    (TauCeti.GeneralLinear.coordinateRingMap K n (detPolynomial (K := K) n)) *
    TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
      (IsLocalization.Away.invSelf (detPolynomial (K := K) n)) = 1
  rw [← map_mul, hraw, map_one]

/-- Differentiating the determinant-inverse coordinate keeps its denominator power. -/
theorem leftTangentOperator_detInverseCoordinate
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K)) :
    leftTangentOperator d (detInverseCoordinate (K := K) n) =
      -(scalarTangentLinear d
        (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n))) •
        detInverseCoordinate (K := K) n := by
  let Δ := Matrix.det (TauCeti.GeneralLinear.genericMatrix K n)
  let u := detInverseCoordinate (K := K) n
  have hu : Δ * u = 1 := GLCoordinateAction.genericMatrix_mul_detInverseCoordinate n
  have hΔ : IsUnit Δ := isUnit_iff_exists_inv.mpr ⟨u, hu⟩
  have hleib : Δ * leftTangentOperator d u +
      u * leftTangentOperator d Δ = 0 := by
    have h := congrArg (leftTangentOperator d) hu
    simpa only [leftTangentOperator_mul,
      show leftTangentOperator d (1 : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) = 0
        from (leftTangentDerivation d).map_one_eq_zero,
      add_comm] using h
  apply hΔ.mul_left_cancel
  calc
    Δ * leftTangentOperator d u = -(u * leftTangentOperator d Δ) :=
      eq_neg_of_add_eq_zero_left hleib
    _ = Δ * (-(scalarTangentLinear d Δ) • u) := by
      rw [leftTangentOperator_det_genericMatrix]
      simp only [Algebra.smul_def, map_neg]
      ring


end ReductiveGroups

