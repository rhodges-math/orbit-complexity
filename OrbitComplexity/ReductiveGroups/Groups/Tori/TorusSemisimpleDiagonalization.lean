import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusDiagonalizableOvergroup
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Basis.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight

/-!
# Torus Semisimple Diagonalization

Simultaneous diagonalization needed for a split torus and one commuting
semisimple tangent operator. -/

noncomputable section
namespace ReductiveGroups
open Module

variable {K V ι : Type*} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem simultaneous_eigenvectors_span
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j))
    (hsemi : ∀ i, Module.End.IsSemisimple (f i)) :
    Submodule.span K
      {v : V | ∃ χ : ι → K, ∀ i, f i v = χ i • v} = ⊤ := by
  have htri (i : ι) :
      (⨆ μ : K, (f i).maxGenEigenspace μ) = ⊤ := by
    simpa only [(hsemi i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using
      (hsemi i).iSup_eigenspace_eq_top
  have hsim :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm htri
  have heq (χ : ι → K) :
      (⨅ i, (f i).maxGenEigenspace (χ i)) =
        (⨅ i, (f i).eigenspace (χ i)) := by
    congr 1
    funext i
    exact (hsemi i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace (χ i)
  simp_rw [heq] at hsim
  apply top_unique
  rw [← hsim]
  refine iSup_le fun χ => ?_
  intro v hv
  apply Submodule.subset_span
  refine ⟨χ, ?_⟩
  intro i
  have hi : v ∈ (f i).eigenspace (χ i) := by
    exact (Submodule.mem_iInf (fun i => (f i).eigenspace (χ i))).mp hv i
  exact Module.End.mem_eigenspace_iff.mp hi

/-- A commuting family of semisimple endomorphisms has a common eigenbasis.
The index is a subset of the original vector space; a later finite-dimensional
reindexing can make it a standard finite basis. -/
theorem exists_simultaneous_eigenbasis
    (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j))
    (hsemi : ∀ i, Module.End.IsSemisimple (f i)) :
    ∃ t : Set V, ∃ b : Basis t K V,
      ∀ j : t, ∃ χ : ι → K, ∀ i, f i (b j) = χ i • b j := by
  let S : Set V := {v | ∃ χ : ι → K, ∀ i, f i v = χ i • v}
  obtain ⟨t, ht, hspan, hli⟩ := exists_linearIndependent K S
  have htop : Submodule.span K t = ⊤ := by
    rw [hspan]
    exact simultaneous_eigenvectors_span f hcomm hsemi
  have hrange : Set.range (Subtype.val : t → V) = t := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  let b : Basis t K V := Basis.mk hli (by
    simpa only [hrange] using htop.ge)
  refine ⟨t, b, ?_⟩
  intro j
  have hj : (j : V) ∈ S := ht j.property
  simpa only [b, Basis.mk_apply, S, Set.mem_ofPred_eq] using hj

open scoped TensorProduct

private def standardGLCoact (K : Type*) [Field K] (n : ℕ) :
    (Fin n → K) →ₗ[K]
      (Fin n → K) ⊗[K] TauCeti.GeneralLinear.coordinateHopfAlgebra K n :=
  (Pi.basisFun K (Fin n)).constr K
    (fun j => ∑ i : Fin n,
      (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        TauCeti.GeneralLinear.genericMatrix K n i j)

private theorem standardGLCoact_basis (K : Type*) [Field K]
    (n : ℕ) (j : Fin n) :
    standardGLCoact K n (Pi.basisFun K (Fin n) j) =
      ∑ i : Fin n,
        (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
          TauCeti.GeneralLinear.genericMatrix K n i j := by
  simp only [standardGLCoact, Basis.constr_basis]

@[instance_reducible]
private def standardGLComodule (K : Type*) [Field K] (n : ℕ) :
    TauCeti.Comodule K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (Fin n → K) where
  coact := standardGLCoact K n
  coassoc := by
    apply (Pi.basisFun K (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, standardGLCoact_basis, map_sum,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    simp_rw [TauCeti.GeneralLinear.genericMatrix_apply,
      TauCeti.GeneralLinear.coordinateHopfAlgebra_comul_X]
    simp_rw [TensorProduct.sum_tmul]
    simp only [map_sum]
    simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
    simp_rw [TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  lTensor_counit_comp_coact := by
    apply (Pi.basisFun K (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, standardGLCoact_basis, map_sum,
      LinearMap.lTensor_tmul]
    simp_rw [TauCeti.GeneralLinear.genericMatrix_apply,
      TauCeti.GeneralLinear.coordinateHopfAlgebra_counit_X]
    simp_rw [TensorProduct.tmul_ite]
    simp

private theorem standardGLComodule_coefficientMatrix
    (K : Type*) [Field K] (n : ℕ) :
    letI : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
        standardGLComodule K n
    TauCeti.Comodule.coefficientMatrix
      (C := TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (Pi.basisFun K (Fin n)) =
        TauCeti.GeneralLinear.genericMatrix K n := by
  let _ : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
    standardGLComodule K n
  ext i j
  rw [TauCeti.Comodule.coefficientMatrix_apply,
    TauCeti.Comodule.matrixCoefficient_def]
  simp only [TauCeti.Comodule.coact,
    standardGLCoact_basis, map_sum, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, Basis.coord_apply]
  simp_rw [TauCeti.GeneralLinear.genericMatrix_apply]
  simp only [Basis.repr_self_apply, LinearMap.id_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private def comodulePointOperator
    (K G V : Type*) [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [TauCeti.Comodule K (MonoidAlgebra K G) V]
    (g : MonoidAlgebra K G →ₐ[K] K) : Module.End K V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id g.toLinearMap) ∘ₗ
      TauCeti.Comodule.coact (R := K) (C := MonoidAlgebra K G) (M := V)

private theorem comodulePointOperator_weight
    (K G V : Type*) [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [TauCeti.Comodule K (MonoidAlgebra K G) V]
    (g : MonoidAlgebra K G →ₐ[K] K) (m : G) {v : V}
    (hv : v ∈ TauCeti.Comodule.weightSpace K G V m) :
    comodulePointOperator K G V g v =
      g (MonoidAlgebra.single m (1 : K)) • v := by
  rw [comodulePointOperator, LinearMap.comp_apply, LinearMap.comp_apply,
    TauCeti.Comodule.mem_weightSpace.mp hv]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe,
    AlgHom.toLinearMap_apply, TensorProduct.rid_tmul]

private theorem semisimple_of_eigenspaces_span
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V)
    (hspan : (⨆ ξ : K, Module.End.eigenspace f ξ) = ⊤) :
    Module.End.IsSemisimple f := by
  let P (ξ : K) : Submodule (Polynomial K) (Module.AEval' f) :=
    Module.AEval.mapSubmodule K V f
      ⟨Module.End.eigenspace f ξ, Module.End.eigenspace_mem_invtSubmodule f ξ⟩
  have hP (ξ : K) : IsSemisimpleModule (Polynomial K) (P ξ) := by
    have heig : Module.End.IsSemisimple
        (f.restrict (Module.End.eigenspace_mem_invtSubmodule f ξ)) := by
      rw [Module.End.restrict_eigenspace]
      exact Module.End.IsSemisimple_smul ξ Module.End.isSemisimple_id
    exact (Module.AEval.restrict_equiv_mapSubmodule f
      (Module.End.eigenspace f ξ)
      (Module.End.eigenspace_mem_invtSubmodule f ξ)).isSemisimpleModule_iff.mp heig
  have htop : (⨆ ξ : K, P ξ) = ⊤ := by
    apply top_unique
    intro z _
    let Q : Submodule (Polynomial K) (Module.AEval' f) := ⨆ ξ, P ξ
    have hle (ξ : K) : Module.End.eigenspace f ξ ≤
        (((Module.AEval.mapSubmodule K V f).symm Q : f.invtSubmodule) :
          Submodule K V) := by
      have hh := (Module.AEval.mapSubmodule K V f).symm.monotone
        (le_iSup P ξ)
      simp only [P, OrderIso.symm_apply_apply] at hh
      exact hh
    have hz : (Module.AEval.of K V f).symm z ∈
        (((Module.AEval.mapSubmodule K V f).symm Q : f.invtSubmodule) :
          Submodule K V) := by
      apply (iSup_le hle)
      rw [hspan]
      trivial
    have hz' : z ∈ Q := by
      simpa only [Module.AEval.mem_mapSubmodule_symm_apply,
        LinearEquiv.apply_symm_apply] using hz
    exact hz'
  exact isSemisimpleModule_of_isSemisimpleModule_submodule' hP htop

private theorem comodulePointOperator_isSemisimple
    (K G V : Type*) [Field K] [CommGroup G] [AddCommGroup V] [Module K V]
    [TauCeti.Comodule K (MonoidAlgebra K G) V]
    (g : MonoidAlgebra K G →ₐ[K] K) :
    Module.End.IsSemisimple (comodulePointOperator K G V g) := by
  apply semisimple_of_eigenspaces_span
  apply top_unique
  rw [← TauCeti.Comodule.iSup_weightSpace_eq_top K G V]
  refine iSup_le fun m => ?_
  intro v hv
  exact Submodule.mem_iSup_of_mem
    (g (MonoidAlgebra.single m (1 : K)))
    (Module.End.mem_eigenspace_iff.mpr
      (comodulePointOperator_weight K G V g m hv))

private theorem standardGLCorestrictedCoact_basis
    (K G : Type*) [Field K] [CommGroup G] (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G) (j : Fin n) :
    (letI : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
        standardGLComodule K n
     letI : TauCeti.Comodule K (MonoidAlgebra K G) (Fin n → K) :=
        TauCeti.Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
     TauCeti.Comodule.coact (R := K) (C := MonoidAlgebra K G)
       (M := Fin n → K) (Pi.basisFun K (Fin n) j)) =
      ∑ i : Fin n, (Pi.basisFun K (Fin n) i) ⊗ₜ[K]
        q (TauCeti.GeneralLinear.genericMatrix K n i j) := by
  let _ : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
    standardGLComodule K n
  let _ : TauCeti.Comodule K (MonoidAlgebra K G) (Fin n → K) :=
    TauCeti.Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
  rw [TauCeti.Comodule.corestrict_coact_apply]
  change (TensorProduct.map LinearMap.id q.toLinearMap)
      (standardGLCoact K n (Pi.basisFun K (Fin n) j)) = _
  rw [standardGLCoact_basis]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    CoalgHom.toLinearMap_eq_ofClass]
  rfl

private theorem StandardGLCorestrictedPointOperator.eq_matrix
    (K G : Type*) [Field K] [CommGroup G] (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G)
    (g : MonoidAlgebra K G →ₐ[K] K) :
    (letI : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
        standardGLComodule K n
     letI : TauCeti.Comodule K (MonoidAlgebra K G) (Fin n → K) :=
        TauCeti.Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
     comodulePointOperator K G (Fin n → K) g) =
      Matrix.toLin'
        ((TauCeti.GeneralLinear.genericMatrix K n).map
          (g.comp (q : _ →ₐ[K] _))) := by
  let _ : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
    standardGLComodule K n
  let _ : TauCeti.Comodule K (MonoidAlgebra K G) (Fin n → K) :=
    TauCeti.Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
  apply (Pi.basisFun K (Fin n)).ext
  intro j
  change (TensorProduct.rid K (Fin n → K))
      (TensorProduct.map LinearMap.id g.toLinearMap
        (TauCeti.Comodule.coact (R := K) (C := MonoidAlgebra K G)
          (M := Fin n → K) (Pi.basisFun K (Fin n) j))) = _
  rw [standardGLCorestrictedCoact_basis K G n q j]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, TensorProduct.rid_tmul,
    Matrix.toLin'_apply, Pi.basisFun_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Every point of a split diagonalizable group acts semisimply in
its finite-dimensional matrix representation. -/
theorem torusMatrixPoint_isSemisimple
    (K G : Type*) [Field K] [CommGroup G] (n : ℕ)
    (q : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
      MonoidAlgebra K G)
    (g : MonoidAlgebra K G →ₐ[K] K) :
    Module.End.IsSemisimple
      (Matrix.toLin'
        ((TauCeti.GeneralLinear.genericMatrix K n).map
          (g.comp (q : _ →ₐ[K] _)))) := by
  let _ : TauCeti.Comodule K
      (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) (Fin n → K) :=
    standardGLComodule K n
  let _ : TauCeti.Comodule K (MonoidAlgebra K G) (Fin n → K) :=
    TauCeti.Comodule.Corestrict (M := Fin n → K) q.toCoalgHom
  rw [← StandardGLCorestrictedPointOperator.eq_matrix K G n q g]
  exact comodulePointOperator_isSemisimple K G (Fin n → K) g

end ReductiveGroups
