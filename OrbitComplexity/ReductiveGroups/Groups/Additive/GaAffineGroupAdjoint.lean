import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Lie.Exponential.InjectiveAdjointExponential

/-!
# Ga Affine Group Adjoint

The adjoint of an additive subgroup is its finite Lie exponential. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K B : Type*} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- The tangent of any additive-group morphism into a finite-type
affine group has nilpotent adjoint. Faithfulness is derived from finite type. -/
theorem gaAffineGroupTangent_ad_nilpotent
    (x : B →ₐc[K] SymmetricAlgebra K K) :
    IsNilpotent (LieAlgebra.ad K
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
      (gaAffineGroupTangent x)) := by
  obtain ⟨n, ρ, _, hρ⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  exact InjectiveAdjointExponential.ad_of_injective_representation
    (affineGroupMatrixDifferential n ρ) hρ (gaAffineGroupTangent x)
    (gaAffineGroupTangent_matrix_nilpotent n x ρ)

/-- The adjoint action of a point on an additive subgroup equals the
finite exponential of the tangent adjoint.  -/
theorem gaAffineGroup_adjoint_eq_exponential
    (x : B →ₐc[K] SymmetricAlgebra K K) (t : K)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    Derivation.adDerivation K
      ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm
        (gaAffineGroupPoints x (Multiplicative.ofAdd t))) d =
      nilpotentLieAdjointExponential (gaAffineGroupTangent x)
        (gaAffineGroupTangent_ad_nilpotent x) t d := by
  obtain ⟨n, ρ, _, hρ⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply hρ
  rw [affineGroupMatrixDifferential_adjoint]
  have hneg :
      TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ
          (gaAffineGroupPoints x (Multiplicative.ofAdd (-t)))) =
      (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ
          (gaAffineGroupPoints x (Multiplicative.ofAdd t))))⁻¹ := by
    change TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain ρ
        (gaAffineGroupPoints x ((Multiplicative.ofAdd t)⁻¹))) = _
    simp only [map_inv]
  rw [← hneg, GaAffineGroupPoints.matrix_eq_exponential,
    GaAffineGroupPoints.matrix_eq_exponential]
  have h := NilpotentLieAdjointExponential.representation
    (affineGroupMatrixDifferential n ρ) hρ (gaAffineGroupTangent x)
    (gaAffineGroupTangent_matrix_nilpotent n x ρ) t d
  simpa only [neg_smul] using h.symm

end ReductiveGroups
