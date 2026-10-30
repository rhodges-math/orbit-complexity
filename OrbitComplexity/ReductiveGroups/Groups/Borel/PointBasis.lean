import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentMatrix
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentCharacters
import OrbitComplexity.ReductiveGroups.Groups.Representations.MatrixInvariantFlags
import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableLieTriangularBasis
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootGeneration
import OrbitComplexity.ReductiveGroups.Groups.Solvable.ConnectedGeneratedPointClosure
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPointUnipotence

/-! # Represented points, bases and diagonal character relations -/

noncomputable section
namespace ReductiveGroups.TorusUnipotent

open TauCeti WithConv Module CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

section Representation

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The matrix of a `K`-point in the coordinate representation `ρ`,
re-expressed in the basis `b` of `Kⁿ`. -/
def pointBasisMatrix (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (g : WithConv (B →ₐ[K] K)) :
    Matrix (Fin n) (Fin n) K :=
  matrixBasisConj b
    (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) : Matrix (Fin n) (Fin n) K)

/-- The equality is

```lean
pointBasisMatrix n ρ b (g * h) = pointBasisMatrix n ρ b g * pointBasisMatrix n ρ b h
```
-/
theorem pointBasisMatrix_mul (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (g h : WithConv (B →ₐ[K] K)) :
    pointBasisMatrix n ρ b (g * h) = pointBasisMatrix n ρ b g * pointBasisMatrix n ρ b h := by
  simp only [pointBasisMatrix, map_mul, Units.val_mul]

/-- The equality is

```lean
pointBasisMatrix n ρ b 1 = 1
```
-/
theorem pointBasisMatrix_one (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) :
    pointBasisMatrix n ρ b 1 = 1 := by
  simp only [pointBasisMatrix, map_one, Units.val_one]

/-- The two matrices of a point and of its inverse multiply to the identity. -/
theorem pointBasisMatrix_mul_inv (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (g : WithConv (B →ₐ[K] K)) :
    pointBasisMatrix n ρ b g * pointBasisMatrix n ρ b g⁻¹ = 1 := by
  rw [← pointBasisMatrix_mul, mul_inv_cancel, pointBasisMatrix_one]

/-- Unipotence of the represented matrix is independent of the basis. -/
theorem pointBasisMatrix_sub_one_pow_eq_zero_iff (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (g : WithConv (B →ₐ[K] K)) (m : ℕ) :
    (pointBasisMatrix n ρ b g - 1) ^ m = 0 ↔
      ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K) - 1) ^ m = 0 := by
  have h : pointBasisMatrix n ρ b g - 1 = matrixBasisConj b
      ((GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [h, matrixBasisConj_pow_eq_zero_iff]

/-- Each entry of the re-expressed matrix is a coordinate function
of the original group. -/
def pointBasisEntry (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (i j : Fin n) : B :=
  matrixLinearFormValue (matrixBasisConjEntry b i j)
    ((GeneralLinear.genericMatrix K n).map ρ)

/-- The equality is

```lean
g.ofConv (pointBasisEntry n ρ b i j) = pointBasisMatrix n ρ b g i j
```
-/
theorem pointBasisEntry_apply (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Basis (Fin n) K (Fin n → K)) (i j : Fin n) (g : WithConv (B →ₐ[K] K)) :
    g.ofConv (pointBasisEntry n ρ b i j) = pointBasisMatrix n ρ b g i j := by
  have hmatrix : ((GeneralLinear.genericMatrix K n).map ρ).map g.ofConv =
      (GeneralLinear.pointsMulEquiv n (AlgHom.mapDomain ρ g) :
        Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.map_map]
    exact GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear n
      (g.ofConv.comp ρ.toAlgHom)
  rw [pointBasisEntry, matrixLinearFormValue_map, hmatrix, matrixLinearFormValue_self,
    matrixBasisConjEntry_apply]
  rfl

end Representation

section Relations

variable {K : Type*} [Field K] {n : ℕ}

/-- Integral monomial relations among nonzero field elements are polynomial
identities between the positive and negative parts of the exponents. -/
theorem prod_zpow_eq_one_iff (a : Fin n → K) (ha : ∀ k, a k ≠ 0) (m : Fin n → ℤ) :
    ∏ k, a k ^ m k = 1 ↔
      ∏ k, a k ^ (m k).toNat = ∏ k, a k ^ (-m k).toNat := by
  have hsplit : ∏ k, a k ^ m k =
      (∏ k, a k ^ (m k).toNat) / ∏ k, a k ^ (-m k).toNat := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (m k)]
    rw [zpow_sub₀ (ha k), zpow_natCast, zpow_natCast]
  have hne : ∏ k, a k ^ (-m k).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (ha k)
  rw [hsplit, div_eq_one_iff_eq hne]

end Relations

end TorusUnipotent
