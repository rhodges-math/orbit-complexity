import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import OrbitComplexity.ReductiveGroups.Groups.Tangents.AffineGroupMatrixDifferential
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Ga Affine Group Points

Points and tangent of an additive subgroup of an affine group. -/

noncomputable section
namespace ReductiveGroups
open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The point homomorphism of the original affine group induced by its
coordinate Hopf morphism from the additive group. -/
def gaAffineGroupPoints (x : B →ₐc[K] SymmetricAlgebra K K) :
    Multiplicative K →* WithConv (B →ₐ[K] K) :=
  (TauCeti.AlgHom.mapDomain x).comp
    (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm.toMonoidHom

/-- The original group's tangent vector obtained by differentiating the
same additive-group coordinate morphism at the origin. -/
def gaAffineGroupTangent (x : B →ₐc[K] SymmetricAlgebra K K) :
    Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K) :=
  TauCeti.derivationComp (B := K) x (gaOriginDerivation K)

/-- Representing an original-group additive point agrees with the point
of the composite coordinate morphism into `GLₙ`. -/
theorem gaAffineGroupPoints_map_matrix (n : ℕ)
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (t : K) :
    TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ
          (gaAffineGroupPoints x (Multiplicative.ofAdd t))) =
      gaMatrixPoints n (x.comp ρ) (Multiplicative.ofAdd t) := by
  simp only [gaAffineGroupPoints, gaMatrixPoints, MonoidHom.comp_apply]
  rw [TauCeti.AlgHom.mapDomain_comp]
  rfl

variable [CharZero K]

/-- The represented tangent of the original additive subgroup is an
associatively nilpotent matrix. -/
theorem gaAffineGroupTangent_matrix_nilpotent (n : ℕ)
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    IsNilpotent (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)) := by
  rw [affineGroupMatrixDifferential_apply, gaAffineGroupTangent]
  have h := gaMatrix_differential_nilpotent n (x.comp ρ)
  rw [TauCeti.derivationComp_comp, LinearMap.comp_apply] at h
  exact h

/-- Every represented point of the original additive subgroup equals
the finite exponential of its represented tangent. -/
theorem GaAffineGroupPoints.matrix_eq_exponential (n : ℕ)
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (t : K) :
    (TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain ρ
        (gaAffineGroupPoints x (Multiplicative.ofAdd t))) :
          Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K)
        (t • affineGroupMatrixDifferential n ρ (gaAffineGroupTangent x)) := by
  rw [gaAffineGroupPoints_map_matrix, GaMatrixPoints.eq_exponential_differential,
    gaAffineGroupTangent, affineGroupMatrixDifferential_apply]
  rw [TauCeti.derivationComp_comp, LinearMap.comp_apply]

end ReductiveGroups
