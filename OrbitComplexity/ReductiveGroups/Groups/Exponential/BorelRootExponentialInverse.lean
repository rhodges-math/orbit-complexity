import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialBijection
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixLogarithm

/-!
# Borel Root Exponential Inverse

The inverse of the Borel unipotent exponential has an explicit
finite polynomial matrix formula, uniformly with cutoff the matrix size. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Every representation of the inverse tangent is computed by
the finite logarithm of the same original group point. The representation
need not be faithful, and no logarithm branch or limiting process occurs. -/
theorem BorelRootUnipotentExponential.inverse_matrix
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K))
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    affineGroupMatrixDifferential n ρ
      ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g).val =
      ∑ k ∈ Finset.range n, ((-1 : K) ^ k / (k + 1 : K)) •
        ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g.val) :
          Matrix (Fin n) (Fin n) K) - 1) ^ (k + 1) := by
  let d := (borelRootUnipotentExponentialEquiv J hJ π hπ).symm g
  have hp : gaAffineGroupPoints
      (borelRootUnipotentGa J hJ π hπ d.val d.property)
        (Multiplicative.ofAdd 1) = g.val := by
    exact congrArg Subtype.val
      ((borelRootUnipotentExponentialEquiv J hJ π hπ).apply_symm_apply g)
  have hpow : ((GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ (gaAffineGroupPoints
        (borelRootUnipotentGa J hJ π hπ d.val d.property)
          (Multiplicative.ofAdd 1))) : Matrix (Fin n) (Fin n) K) - 1) ^ (n + 1) = 0 := by
    rw [hp, pow_succ,
      BorelRootUnipotentPoint.matrix_pow_sub_one_eq_zero J hJ π hπ n ρ g.val g.property,
      zero_mul]
  have h := GaAffineGroupTangent.matrix_eq_finite_logarithm n
    (borelRootUnipotentGa J hJ π hπ d.val d.property) ρ n hpow
  rw [borelRootUnipotentGa_tangent, hp] at h
  exact h

end ReductiveGroups
