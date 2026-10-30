import OrbitComplexity.ReductiveGroups.Groups.Additive.PolynomialPointGaIntegration
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentPowerCurveLaw

/-!
# Unipotent Point Ga Integration

Every point represented by a unipotent matrix in a closed embedding
lies on a unique Ga morphism of the original affine group. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- Unipotence in a faithful closed matrix embedding suffices to
construct the Ga morphism through the original point.  -/
theorem UnipotentPointGaIntegration.existsUnique_of_matrix_point_unipotent
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (g : WithConv (B →ₐ[K] K))
    (hg : IsNilpotent ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
      Matrix (Fin n) (Fin n) K) - 1)) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupPoints x (Multiplicative.ofAdd 1) = g := by
  let N : Matrix (Fin n) (Fin n) K :=
    (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
      Matrix (Fin n) (Fin n) K) - 1
  obtain ⟨r, hr⟩ := hg
  have hN : N ^ (r + 1) = 0 := by
    change (((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
      Matrix (Fin n) (Fin n) K) - 1) ^ (r + 1)) = 0
    rw [pow_succ, hr, zero_mul]
  let p := nilpotentPowerPolynomial (K := K) (r + 1) N
  have heval (t : K) : polynomialMatrixValue p t =
      nilpotentPowerCurve (K := K) (r + 1) N t := by
    exact nilpotentPowerPolynomial_eval (K := K) (r + 1) N t
  apply PolynomialPointGaIntegration.existsUnique_of_polynomial_matrix_point n ρ hρ g p
  · rw [heval]
    exact nilpotentPowerCurve_zero (r + 1) N (by omega)
  · intro s t
    simp only [heval]
    exact nilpotentPowerCurve_add (r + 1) N hN s t
  · rw [heval, nilpotentPowerCurve_one (r + 1) N hN]
    dsimp [N]
    abel

end ReductiveGroups
