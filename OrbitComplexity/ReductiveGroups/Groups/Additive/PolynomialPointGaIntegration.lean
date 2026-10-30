import OrbitComplexity.ReductiveGroups.Groups.Additive.PolynomialMatrixGaMorphism
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointDescent

/-!
# Polynomial Point Ga Integration

A polynomial matrix one-parameter group whose unit-parameter point
belongs to a closed affine subgroup integrates inside that original subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- Only the point at parameter one is required to lie in the original
subgroup: the entire Ga morphism then descends to it. -/
theorem PolynomialPointGaIntegration.existsUnique_of_polynomial_matrix_point
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (g : WithConv (B →ₐ[K] K))
    (p : Polynomial (Matrix (Fin n) (Fin n) K))
    (hzero : polynomialMatrixValue p 0 = 1)
    (hadd : ∀ s t : K, polynomialMatrixValue p (s + t) =
      polynomialMatrixValue p s * polynomialMatrixValue p t)
    (hone : polynomialMatrixValue p 1 =
      (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K)) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupPoints x (Multiplicative.ofAdd 1) = g := by
  obtain ⟨φ, hφ, _⟩ := PolynomialMatrixGaMorphism.existsUnique_of_polynomial_matrix_curve
    p hzero hadd (AlgHom.mapDomain ρ g) hone
  obtain ⟨x, hx, _⟩ := GaUnitPointDescent.existsUnique_of_unitPoint_factor ρ hρ φ g hφ
  refine ⟨x, hx.2, ?_⟩
  intro y hy
  exact gaAffineGroupPoints_one_injective (hy.trans hx.2.symm)

end ReductiveGroups
