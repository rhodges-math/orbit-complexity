import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Lie.Roots.RootProductConjugation

/-!
# Ga Affine Group Commutation

Commutation of additive-subgroup points from their tangent bracket. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K B : Type*} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

omit [CharZero K] [Algebra.FiniteType K B] in
private theorem GaAffineGroupCommutation.point_matrixMap_injective_of_surjective (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) :
    Function.Injective
      (TauCeti.AlgHom.mapDomain ρ :
        WithConv (B →ₐ[K] K) →*
          WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K)) := by
  intro p q hpq
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hρ b
  have h := congrArg (fun z : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K) => z.ofConv a) hpq
  simpa only [TauCeti.AlgHom.mapDomain_apply_apply] using h

/-- Two additive-subgroup point families commute when their
tangent vectors have zero Lie bracket. The matrix representation and its
faithfulness are derived from finite type. -/
theorem GaAffineGroupPoints.commute_of_tangent_bracket_zero
    (x y : B →ₐc[K] SymmetricAlgebra K K)
    (hxy : ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆ = 0)
    (s t : K) :
    Commute (gaAffineGroupPoints x (Multiplicative.ofAdd s))
      (gaAffineGroupPoints y (Multiplicative.ofAdd t)) := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  let X := affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)
  let Y := affineGroupMatrixDifferential n ρ (gaAffineGroupTangent y)
  have hnilX : IsNilpotent X := gaAffineGroupTangent_matrix_nilpotent n x ρ
  have hnilY : IsNilpotent Y := gaAffineGroupTangent_matrix_nilpotent n y ρ
  have hbracket := (affineGroupMatrixDifferential n ρ).map_lie
    (gaAffineGroupTangent x) (gaAffineGroupTangent y)
  rw [hxy, map_zero] at hbracket
  change 0 = X * Y - Y * X at hbracket
  have hcomm : Commute X Y := sub_eq_zero.mp hbracket.symm
  have hexp : Commute
      (associativeExponential (K := K) (s • X))
      (associativeExponential (K := K) (t • Y)) :=
    associativeExponential_commute (hnilX.smul s) (hnilY.smul t)
      ((hcomm.smul_left s).smul_right t)
  let gx := gaAffineGroupPoints x (Multiplicative.ofAdd s)
  let gy := gaAffineGroupPoints y (Multiplicative.ofAdd t)
  have hgl : Commute
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gx))
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gy)) := by
    apply Units.ext
    change
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gx) :
        Matrix (Fin n) (Fin n) K) *
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gy) :
        Matrix (Fin n) (Fin n) K) =
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gy) :
        Matrix (Fin n) (Fin n) K) *
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ gx) :
        Matrix (Fin n) (Fin n) K)
    change associativeExponential (K := K) (s • X) *
      associativeExponential (K := K) (t • Y) =
      associativeExponential (K := K) (t • Y) *
        associativeExponential (K := K) (s • X) at hexp
    simpa only [gx, gy, X, Y, GaAffineGroupPoints.matrix_eq_exponential] using hexp
  apply GaAffineGroupCommutation.point_matrixMap_injective_of_surjective n ρ hρ
  apply (TauCeti.GeneralLinear.pointsMulEquiv n).injective
  change _ * _ = _ * _ at hgl
  simpa only [gx, gy, map_mul] using hgl

end ReductiveGroups
