import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusInvariantSubspaceDecomposition
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSemisimpleDiagonalization
import OrbitComplexity.ReductiveGroups.Groups.Tangents.AffineGroupMatrixDifferential

/-!
# Torus Matrix Invariant Subspace

The standard matrix comodule, corestricted along a split-torus
coordinate representation, and its point and tangent operators. -/

noncomputable section
namespace ReductiveGroups

open TauCeti
open scoped TensorProduct

/-- The standard `GLₙ` coaction on column vectors. -/
def standardMatrixCoact (K : Type*) [Field K] (n : ℕ) :
    (Fin n → K) →ₗ[K]
      (Fin n → K) ⊗[K] GeneralLinear.coordinateHopfAlgebra K n :=
  (Pi.basisFun K (Fin n)).constr K
    (fun j => ∑ i : Fin n,
      (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        GeneralLinear.genericMatrix K n i j)

/-- The equality is

```lean
standardMatrixCoact K n (Pi.basisFun K (Fin n) j) =
      ∑ i : Fin n, (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        GeneralLinear.genericMatrix K n i j
```
-/
theorem standardMatrixCoact_basis (K : Type*) [Field K]
    (n : ℕ) (j : Fin n) :
    standardMatrixCoact K n (Pi.basisFun K (Fin n) j) =
      ∑ i : Fin n, (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        GeneralLinear.genericMatrix K n i j := by
  simp [standardMatrixCoact]

/-- The standard comodule structure on column vectors `Fin n → K` over the coordinate Hopf algebra
of `GLₙ`, with coaction `e_j ↦ ∑ i, e_i ⊗ X i j`. -/
@[instance_reducible]
def standardMatrixComodule (K : Type*) [Field K] (n : ℕ) :
    Comodule K (GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) where
  coact := standardMatrixCoact K n
  coassoc := by
    apply (Pi.basisFun K (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, standardMatrixCoact_basis, map_sum,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    simp_rw [GeneralLinear.genericMatrix_apply,
      GeneralLinear.coordinateHopfAlgebra_comul_X]
    simp_rw [TensorProduct.sum_tmul]
    simp only [map_sum]
    simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
    simp_rw [TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply (Pi.basisFun K (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, standardMatrixCoact_basis, map_sum,
      LinearMap.lTensor_tmul]
    simp_rw [GeneralLinear.genericMatrix_apply,
      GeneralLinear.coordinateHopfAlgebra_counit_X]
    simp_rw [TensorProduct.tmul_ite]
    simp

/-- The split-torus comodule obtained from a coordinate Hopf map. -/
@[instance_reducible]
def torusMatrixComodule (K : Type*) [Field K] {M : Type*} [CommGroup M]
    (n : ℕ) (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K M) : Comodule K (MonoidAlgebra K M) (Fin n → K) := by
  letI := standardMatrixComodule K n
  exact Comodule.Corestrict (M := Fin n → K) q.toCoalgHom

/-- The coaction of a matrix torus on a standard basis vector is the sum of the basis
vectors tensored with the entries in the corresponding column of the coordinate matrix. -/
theorem torusMatrixCoact_basis (K : Type*) [Field K] {M : Type*} [CommGroup M]
    (n : ℕ) (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K M) (j : Fin n) :
    (letI := torusMatrixComodule K n q
     Comodule.coact (R := K) (C := MonoidAlgebra K M)
       (M := Fin n → K) (Pi.basisFun K (Fin n) j)) =
      ∑ i : Fin n, (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        q (GeneralLinear.genericMatrix K n i j) := by
  let _ : Comodule K (GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
    standardMatrixComodule K n
  let _ : Comodule K (MonoidAlgebra K M) (Fin n → K) :=
    Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
  rw [Comodule.corestrict_coact_apply]
  change (TensorProduct.map LinearMap.id q.toLinearMap)
      (standardMatrixCoact K n (Pi.basisFun K (Fin n) j)) = _
  rw [standardMatrixCoact_basis]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    CoalgHom.toLinearMap_eq_ofClass]
  rfl

/-- Evaluating the torus comodule at a point is the matrix obtained
by evaluating the original coordinate representation. -/
theorem torusMatrixPointOperator_eq_matrix
    (K : Type*) [Field K] {ι : Type*} (n : ℕ)
    (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (g : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K) :
    (letI := torusMatrixComodule K n q
     torusPointOperator (V := Fin n → K) g) =
      Matrix.toLin'
        ((GeneralLinear.genericMatrix K n).map (g.comp (q : _ →ₐ[K] _))) := by
  let _ : Comodule K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Fin n → K) := torusMatrixComodule K n q
  apply (Pi.basisFun K (Fin n)).ext
  intro j
  change (TensorProduct.rid K (Fin n → K))
      (TensorProduct.map LinearMap.id g.toLinearMap
        (Comodule.coact (R := K)
          (C := MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
          (M := Fin n → K) (Pi.basisFun K (Fin n) j))) = _
  rw [torusMatrixCoact_basis K n q j]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, TensorProduct.rid_tmul,
    Matrix.toLin'_apply, Pi.basisFun_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Differentiating the same comodule is the matrix
differential of its coordinate Hopf map. -/
theorem torusMatrixTangentOperator_eq_matrix
    (K : Type*) [Field K] {ι : Type*} (n : ℕ)
    (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K)) :
    (letI := torusMatrixComodule K n q
     torusTangentOperator (V := Fin n → K) h) =
      Matrix.toLin' (affineGroupMatrixDifferential n q h) := by
  let _ : Comodule K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Fin n → K) := torusMatrixComodule K n q
  apply (Pi.basisFun K (Fin n)).ext
  intro j
  change (TensorProduct.rid K (Fin n → K))
      (TensorProduct.map LinearMap.id
        ((Bialgebra.CounitAlgebra.algEquivSelf K
          (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K).toLinearMap.comp
            h.toLinearMap)
        (Comodule.coact (R := K)
          (C := MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
          (M := Fin n → K) (Pi.basisFun K (Fin n) j))) = _
  rw [torusMatrixCoact_basis K n q j]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.rid_tmul, Matrix.toLin'_apply, Pi.basisFun_apply]
  ext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply]
  change (∑ c : Fin n,
      (Bialgebra.CounitAlgebra.algEquivSelf K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K
          (h (q (GeneralLinear.genericMatrix K n c j)))) •
        (if i = c then (1 : K) else 0)) = _
  simp only [smul_ite, smul_zero]
  simp [affineGroupMatrixDifferential_apply, GeneralLinear.tangentMatrix_apply,
    GeneralLinear.genericMatrix_apply]
  have hscalar :
      (Bialgebra.CounitAlgebra.algEquivSelf K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K
        (h (q (GeneralLinear.genericMatrix K n i j)))) • (1 : K) =
          Bialgebra.CounitAlgebra.algEquivSelf K
            (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K
            (h (q (GeneralLinear.genericMatrix K n i j))) := by
      simp only [smul_eq_mul, mul_one]
  change (Bialgebra.CounitAlgebra.algEquivSelf K
    (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K
      (h (q (GeneralLinear.genericMatrix K n i j)))) • 1 = _
  rw [hscalar]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply K
    (GeneralLinear.coordinateHopfAlgebra K n) K
    (h (q (GeneralLinear.genericMatrix K n i j)))).symm

/-- A matrix subspace stable under every represented torus tangent
is stable under every represented torus point. -/
theorem torusMatrixPoint_preserves_of_tangent
    (K : Type*) [Field K] [CharZero K] {ι : Type*} (n : ℕ)
    (q : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (W : Submodule K (Fin n → K))
    (hW : ∀ h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      ∀ v ∈ W, Matrix.toLin' (affineGroupMatrixDifferential n q h) v ∈ W)
    (g : MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K)
    (v : Fin n → K) (hv : v ∈ W) :
    Matrix.toLin'
      ((GeneralLinear.genericMatrix K n).map (g.comp (q : _ →ₐ[K] _))) v ∈ W := by
  let _ : Comodule K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Fin n → K) := torusMatrixComodule K n q
  have hW' : ∀ h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      ∀ v ∈ W, torusTangentOperator h v ∈ W := by
    intro h x hx
    rw [torusMatrixTangentOperator_eq_matrix K n q h]
    exact hW h x hx
  have hp := torusPointOperator_preserves_of_tangent W hW' g v hv
  rwa [torusMatrixPointOperator_eq_matrix K n q g] at hp

end ReductiveGroups
