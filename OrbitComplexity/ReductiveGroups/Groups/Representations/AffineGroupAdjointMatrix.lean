import OrbitComplexity.ReductiveGroups.Groups.Tangents.AffineGroupMatrixDifferential
import OrbitComplexity.ReductiveGroups.Groups.Tangents.AdjointDifferentialNaturality
import OrbitComplexity.ReductiveGroups.Groups.Representations.GeneralLinearAdjointMatrix

/-!
# Affine Group Adjoint Matrix

The original affine group's adjoint action is carried by its
representation differential to conjugation of matrices. -/

noncomputable section
namespace ReductiveGroups
open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Adjoint equivariance for a matrix representation of the original affine
group. Both the tangent map and the mapped group point are constructed from
the same coordinate bialgebra morphism. -/
theorem affineGroupMatrixDifferential_adjoint (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (g : WithConv (B →ₐ[K] K))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupMatrixDifferential n ρ
      (Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) d) =
      (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K) * affineGroupMatrixDifferential n ρ d *
      ((TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ g))⁻¹ :
        Matrix.GeneralLinearGroup (Fin n) K) := by
  rw [affineGroupMatrixDifferential_apply, derivationComp_adDerivation,
    generalLinear_tangentMatrix_adDerivation]
  simp only [generalLinearCounitPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, affineGroupMatrixDifferential_apply]

end ReductiveGroups
