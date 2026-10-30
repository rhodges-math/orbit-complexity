import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaCoefficientConvolution
import OrbitComplexity.ReductiveGroups.Groups.Tangents.TangentConvolutionPowers
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints

/-!
# Ga Tangent Determines Morphism

An additive-group morphism is determined by its tangent in
characteristic zero. Its coordinate map kills every kernel through which
that tangent factors. -/

noncomputable section
namespace ReductiveGroups

variable {K A B : Type*} [Field K] [CharZero K]
  [CommRing A] [HopfAlgebra K A] [CommRing B] [HopfAlgebra K B]

omit [CharZero K] in
/-- Every coefficient of an additive-group pullback is recovered
from the corresponding convolution power of its tangent. -/
theorem gaMorphism_coefficient_factorial
    (φ : A →ₐc[K] SymmetricAlgebra K K) (n : ℕ) (a : A) :
    (n.factorial : K) * (gaPolynomialEquiv K (φ a)).coeff n =
      tangentConvolutionPower (gaAffineGroupTangent φ) n a := by
  rw [gaAffineGroupTangent, tangentConvolutionPower_comp]
  exact (gaOriginDerivation_pow_coeff K n (φ a)).symm

/-- In characteristic zero, the origin tangent determines the
whole additive-group coordinate morphism. -/
theorem gaMorphism_ext_of_tangent_eq
    (φ ψ : A →ₐc[K] SymmetricAlgebra K K)
    (h : gaAffineGroupTangent φ = gaAffineGroupTangent ψ) : φ = ψ := by
  ext a
  apply (gaPolynomialEquiv K).injective
  ext n
  apply mul_left_cancel₀ (show (n.factorial : K) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [gaMorphism_coefficient_factorial, gaMorphism_coefficient_factorial, h]

/-- If the tangent of a Ga morphism factors through a coordinate
bialgebra map, its entire polynomial coordinate map kills that map's kernel.
This statement does not assume the desired group-level factorization. -/
theorem GaMorphism.kills_kernel_of_tangent_factors
    (ρ : A →ₐc[K] B) (φ : A →ₐc[K] SymmetricAlgebra K K)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hφ : gaAffineGroupTangent φ = TauCeti.derivationComp (B := K) ρ d)
    (a : A) (ha : ρ a = 0) : φ a = 0 := by
  apply (gaPolynomialEquiv K).injective
  rw [map_zero]
  ext n
  rw [Polynomial.coeff_zero]
  apply mul_left_cancel₀ (show (n.factorial : K) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [mul_zero, gaMorphism_coefficient_factorial, hφ,
    tangentConvolutionPower_comp, ha]
  simp [tangentConvolutionPower]
  rfl

end ReductiveGroups
