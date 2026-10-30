import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateTruncation
import OrbitComplexity.ReductiveGroups.Groups.Representations.GLCoordinateAction
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# GL Truncation Stability

Polynomial-degree stability of the GL coordinate tangent action. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] (n : ℕ)
/-- The polynomial row vector field associated to the same tangent. -/
private def rowPolynomialDerivation
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K)) :
    Derivation K (MvPolynomial (Fin n × Fin n) K)
      (MvPolynomial (Fin n × Fin n) K) :=
  MvPolynomial.mkDerivation K fun ij =>
    ∑ k : Fin n,
      TauCeti.GeneralLinear.tangentMatrix n d ij.1 k • MvPolynomial.X (k, ij.2)

private theorem rowPolynomialDerivation_X
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (i j : Fin n) :
    rowPolynomialDerivation n d (MvPolynomial.X (i, j)) =
      ∑ k : Fin n,
        TauCeti.GeneralLinear.tangentMatrix n d i k • MvPolynomial.X (k, j) := by
  simp [rowPolynomialDerivation]

private abbrev polynomialToGL :
    MvPolynomial (Fin n × Fin n) K →ₐ[K]
      TauCeti.GeneralLinear.coordinateHopfAlgebra K n :=
  (TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toAlgHom.comp
    (TauCeti.GeneralLinear.coordinateRingMap K n)

private theorem leftTangentOperator_polynomialToGL
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (p : MvPolynomial (Fin n × Fin n) K) :
    leftTangentOperator d (polynomialToGL (K := K) n p) =
      polynomialToGL (K := K) n (rowPolynomialDerivation n d p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp [rowPolynomialDerivation, polynomialToGL,
        show leftTangentOperator d (algebraMap K
          (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) c) = 0 from
          (leftTangentDerivation d).map_algebraMap c]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rw [map_mul, leftTangentOperator_mul,
        (rowPolynomialDerivation n d).leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hp]
      have hX : polynomialToGL (K := K) n (MvPolynomial.X ij) =
          TauCeti.GeneralLinear.genericMatrix K n ij.1 ij.2 := rfl
      rw [hX, leftTangentOperator_genericMatrix_apply]
      have hrow : polynomialToGL (K := K) n
          (rowPolynomialDerivation n d (MvPolynomial.X ij)) =
          ∑ k : Fin n,
            TauCeti.GeneralLinear.tangentMatrix n d ij.1 k •
              TauCeti.GeneralLinear.genericMatrix K n k ij.2 := by
        rw [rowPolynomialDerivation_X, map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_smul]
        rfl
      rw [hrow]

private theorem rowPolynomialDerivation_X_degree
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (ij : Fin n × Fin n) :
    rowPolynomialDerivation n d (MvPolynomial.X ij) ∈
      glPolynomialDegreeLE (K := K) n 1 := by
  rw [rowPolynomialDerivation_X]
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  change (MvPolynomial.X (k, ij.2) : MvPolynomial (Fin n × Fin n) K).totalDegree ≤ 1
  simp

private theorem rowPolynomialDerivation_monomial_degree
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (m : (Fin n × Fin n) →₀ ℕ) :
    rowPolynomialDerivation n d (MvPolynomial.monomial m 1) ∈
      glPolynomialDegreeLE (K := K) n m.degree := by
  rw [rowPolynomialDerivation]
  rw [MvPolynomial.mkDerivation_monomial]
  simp only [one_smul]
  apply Submodule.sum_mem
  intro ij hij
  have hnonzero : m ij ≠ 0 := Finsupp.mem_support_iff.mp hij
  have hdeg : (m - Finsupp.single ij 1).degree + 1 = m.degree := by
    have h := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel hnonzero)
    simpa [Finsupp.degree_single] using h
  dsimp only
  rw [← rowPolynomialDerivation_X n d ij.1 ij.2]
  simp only [smul_eq_mul]
  change (MvPolynomial.monomial (m - Finsupp.single ij 1) (m ij : K) *
      rowPolynomialDerivation n d (MvPolynomial.X ij)).totalDegree ≤ m.degree
  calc
    (MvPolynomial.monomial (m - Finsupp.single ij 1) (m ij : K) *
        rowPolynomialDerivation n d (MvPolynomial.X ij)).totalDegree ≤
      (MvPolynomial.monomial (m - Finsupp.single ij 1) (m ij : K)).totalDegree +
        (rowPolynomialDerivation n d (MvPolynomial.X ij)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ (m - Finsupp.single ij 1).degree + 1 := by
      apply add_le_add
      · simpa only [Finsupp.degree_apply, Finsupp.sum, Function.id_def] using
          (MvPolynomial.totalDegree_monomial_le
            (m - Finsupp.single ij 1) (m ij : K))
      · exact rowPolynomialDerivation_X_degree n d ij
    _ = m.degree := hdeg

/-- The polynomial row field preserves each exact total-degree filtration piece. -/
private theorem rowPolynomialDerivation_preserves_degree
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (bound : ℕ) (p : MvPolynomial (Fin n × Fin n) K)
    (hp : p ∈ glPolynomialDegreeLE (K := K) n bound) :
    rowPolynomialDerivation n d p ∈ glPolynomialDegreeLE (K := K) n bound := by
  rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro m hm
  have hmdeg : m.degree ≤ bound := (MvPolynomial.le_totalDegree hm).trans hp
  have hmono := rowPolynomialDerivation_monomial_degree n d m
  have hcoeff : rowPolynomialDerivation n d
      (MvPolynomial.monomial m (p.coeff m)) ∈
      glPolynomialDegreeLE (K := K) n m.degree := by
    have hs : (MvPolynomial.monomial m (p.coeff m) :
        MvPolynomial (Fin n × Fin n) K) =
        p.coeff m • MvPolynomial.monomial m 1 := by
      simp [MvPolynomial.smul_monomial]
    rw [hs]
    change (rowPolynomialDerivation n d).toLinearMap
      (p.coeff m • MvPolynomial.monomial m 1) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ _ hmono
  exact hcoeff.trans hmdeg

private theorem LeftTangentOperator.detInverse_pow_scalar
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (r : ℕ) :
    ∃ c : K, leftTangentOperator d ((detInverseCoordinate (K := K) n) ^ r) =
      c • (detInverseCoordinate (K := K) n) ^ r := by
  induction r with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [pow_zero, zero_smul]
      change (leftTangentDerivation d) 1 = 0
      exact (leftTangentDerivation d).map_one_eq_zero
  | succ r ih =>
      obtain ⟨c, hc⟩ := ih
      let a := scalarTangentLinear d
        (Matrix.det (TauCeti.GeneralLinear.genericMatrix K n))
      refine ⟨c - a, ?_⟩
      rw [pow_succ, leftTangentOperator_mul, hc,
        leftTangentOperator_detInverseCoordinate]
      simp only [Algebra.smul_def, map_sub, map_neg]
      ring

/-- Concrete membership in a numerator-degree/denominator-power piece. -/
theorem mem_glCoordinateTruncation_iff
    (r bound : ℕ) (b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :
    b ∈ glCoordinateTruncation (K := K) n r bound ↔
      ∃ p : MvPolynomial (Fin n × Fin n) K,
        p ∈ glPolynomialDegreeLE (K := K) n bound ∧
          b = polynomialToGL (K := K) n p *
            (detInverseCoordinate (K := K) n) ^ r := by
  unfold glCoordinateTruncation
  change (∃ p : glPolynomialDegreeLE (K := K) n bound,
      ((TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n).toLinearEquiv.toLinearMap).comp
        ((LinearMap.mulRight K ((IsLocalization.Away.invSelf
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) ^ r)).comp
          ((TauCeti.GeneralLinear.coordinateRingMap K n).toLinearMap.comp
            (glPolynomialDegreeLE (K := K) n bound).subtype)) p = b) ↔ _
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.1, p.2, ?_⟩
    rw [← hp]
    change TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
      (TauCeti.GeneralLinear.coordinateRingMap K n p.1 *
        (IsLocalization.Away.invSelf
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) ^ r) = _
    simp [polynomialToGL, detInverseCoordinate, map_mul, map_pow]
  · rintro ⟨p, hp, hb⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [hb]
    change TauCeti.GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
      (TauCeti.GeneralLinear.coordinateRingMap K n p *
        (IsLocalization.Away.invSelf
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) ^ r) = _
    simp [polynomialToGL, detInverseCoordinate, map_mul, map_pow]

/-- The left tangent operator preserves each finite-dimensional localization piece. -/
theorem LeftTangentOperator.preserves_glCoordinateTruncation
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K))
    (r bound : ℕ) (b : TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
    (hb : b ∈ glCoordinateTruncation (K := K) n r bound) :
    leftTangentOperator d b ∈ glCoordinateTruncation (K := K) n r bound := by
  obtain ⟨p, hp, rfl⟩ :=
    (mem_glCoordinateTruncation_iff (K := K) n r bound b).mp hb
  obtain ⟨c, hc⟩ := LeftTangentOperator.detInverse_pow_scalar n d r
  let q := rowPolynomialDerivation n d p + c • p
  have hq : q ∈ glPolynomialDegreeLE (K := K) n bound :=
    Submodule.add_mem _ (rowPolynomialDerivation_preserves_degree n d bound p hp)
      (Submodule.smul_mem _ c hp)
  apply (mem_glCoordinateTruncation_iff (K := K) n r bound _).mpr
  refine ⟨q, hq, ?_⟩
  rw [leftTangentOperator_mul, leftTangentOperator_polynomialToGL, hc]
  simp only [q, map_add, Algebra.smul_def, map_mul, AlgHom.commutes]
  ring

end ReductiveGroups

