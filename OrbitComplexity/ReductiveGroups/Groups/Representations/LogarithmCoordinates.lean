import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialInverse
import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixLinearFormExtension

/-!
# Logarithm Coordinates

Finite logarithms are coordinate functions of the original
affine group. On the Borel's unipotent subgroup they recover every linear
form in the represented inverse tangent. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- The finite logarithm matrix whose entries belong to the original
coordinate algebra. It is defined on the whole affine group, although
the inverse-exponential interpretation applies on the unipotent subgroup. -/
def affineGroupLogarithmMatrix (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    Matrix (Fin n) (Fin n) B :=
  ∑ k ∈ Finset.range n, ((-1 : K) ^ k / (k + 1 : K)) •
    ((GeneralLinear.genericMatrix K n).map ρ - 1) ^ (k + 1)

omit [CharZero K] in
/-- Specialization of the coordinate matrix is its finite
logarithm formula on the same original point. -/
theorem affineGroupLogarithmMatrix_point (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (g : WithConv (B →ₐ[K] K)) :
    (affineGroupLogarithmMatrix n ρ).map g.ofConv =
      ∑ k ∈ Finset.range n, ((-1 : K) ^ k / (k + 1 : K)) •
        ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
          Matrix (Fin n) (Fin n) K) - 1) ^ (k + 1) := by
  have hmatrix : ((GeneralLinear.genericMatrix K n).map ρ).map g.ofConv =
      (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.map_map]
    exact GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear n
      (g.ofConv.comp ρ.toAlgHom)
  change g.ofConv.mapMatrix (affineGroupLogarithmMatrix n ρ) = _
  simp only [affineGroupLogarithmMatrix, map_sum, map_smul, map_pow, map_sub, map_one]
  change (∑ k ∈ Finset.range n, ((-1 : K) ^ k / (k + 1 : K)) •
    (((GeneralLinear.genericMatrix K n).map ρ).map g.ofConv - 1) ^ (k + 1)) = _
  rw [hmatrix]

/-- A scalar linear form in the logarithm matrix is a single element
of the original coordinate algebra. -/
def affineGroupLogarithmLinearCoordinate (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (f : Matrix (Fin n) (Fin n) K →ₗ[K] K) : B :=
  matrixLinearFormValue f (affineGroupLogarithmMatrix n ρ)

universe u
variable {K' B' ι : Type u} [Field K'] [IsAlgClosed K'] [CharZero K']
  [CommRing B'] [HopfAlgebra K' B'] [Algebra.FiniteType K' B']

/-- The coordinate function evaluates to the corresponding linear form
of the inverse tangent, in any matrix representation. -/
theorem BorelRootExponentialInverse.linearCoordinate
    (J : HopfIdeal K' B') (hJ : HopfIdeal.IsBorel K' (CommHopfAlgCat.of K' B') J)
    (π : B' →ₐc[K'] MonoidAlgebra K' (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (g : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K' B')
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K' K'))
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K' n →ₐc[K'] B')
    (f : Matrix (Fin n) (Fin n) K' →ₗ[K'] K') :
    g.val.ofConv (affineGroupLogarithmLinearCoordinate n ρ f) =
      f (affineGroupMatrixDifferential n ρ
        ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm g).val) := by
  rw [affineGroupLogarithmLinearCoordinate, matrixLinearFormValue_map,
    matrixLinearFormValue_self, affineGroupLogarithmMatrix_point,
    ← BorelRootUnipotentExponential.inverse_matrix J hJ π hπ g n ρ]

end ReductiveGroups
