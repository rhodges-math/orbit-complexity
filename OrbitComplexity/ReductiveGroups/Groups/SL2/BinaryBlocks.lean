import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryStandard
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Lie.Sl2.Decomposition
import Mathlib.Data.Matrix.Block

/-! # Finite sums of algebraic binary-form representations -/

noncomputable section

namespace ReductiveGroups.BinaryForms

open TauCeti Module
open scoped TensorProduct

universe u v
variable (R : Type u) [CommRing R]

private def blockCoefficients {k : ℕ} (n : Fin k → ℕ) :
    Matrix (Σ i, Fin (n i + 1)) (Σ i, Fin (n i + 1))
      (SpecialLinear.coordinateHopfAlgebra R 2) :=
  Matrix.blockDiagonal' fun i =>
    (GeneralLinear.genericMatrix R (n i + 1)).map (coordinateMap R (n i))

private theorem block_comul {k : ℕ} (n : Fin k → ℕ) :
    (blockCoefficients R n).map
        (Bialgebra.comulAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) =
      (blockCoefficients R n).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (blockCoefficients R n).map (Algebra.TensorProduct.includeRight (R := R)) := by
  classical
  simp only [blockCoefficients, Matrix.blockDiagonal'_map _ _ (map_zero _)]
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  exact Comodule.map_comul_map R (GeneralLinear.genericMatrix R (n i + 1))
    (coordinateMap R (n i)) (GeneralLinear.map_comul_genericMatrix R (n i + 1))

private theorem block_counit {k : ℕ} (n : Fin k → ℕ) :
    (blockCoefficients R n).map
        (Bialgebra.counitAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) = 1 := by
  classical
  rw [blockCoefficients, Matrix.blockDiagonal'_map _ _ (map_zero _)]
  have h (i : Fin k) :
      ((GeneralLinear.genericMatrix R (n i + 1)).map (coordinateMap R (n i))).map
        (Bialgebra.counitAlgHom R (SpecialLinear.coordinateHopfAlgebra R 2)) = 1 :=
    Comodule.map_counit_map R (GeneralLinear.genericMatrix R (n i + 1))
      (coordinateMap R (n i)) (GeneralLinear.map_counit_genericMatrix R (n i + 1))
  simp only [h]
  exact Matrix.blockDiagonal'_one

@[instance_reducible]
private def blockComodule {k : ℕ} (n : Fin k → ℕ) :
    Comodule R (SpecialLinear.coordinateHopfAlgebra R 2) ((Σ i, Fin (n i + 1)) → R) :=
  Comodule.matrixComodule R (blockCoefficients R n) (block_comul R n)
    (Comodule.counit_basisFun_of_map_counit R _ (block_counit R n))

variable (K : Type u) [Field K]

private def tangentOperator {H : Type v} [CommRing H] [Bialgebra K H]
    {M : Type*} [AddCommGroup M] [Module K M] [Comodule K H M]
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) : Module.End K M :=
  (TensorProduct.rid K M).toLinearMap.comp
    ((TensorProduct.map LinearMap.id
      ((Bialgebra.CounitAlgebra.algEquivSelf K H K).toLinearMap.comp d.toLinearMap)).comp
        (Comodule.coact (R := K) (C := H) (M := M)))

private theorem tangentOperator_transport {H : Type v} [CommRing H] [Bialgebra K H]
    {M N : Type*} [AddCommGroup M] [Module K M] [Comodule K H M]
    [AddCommGroup N] [Module K N] (e : M ≃ₗ[K] N)
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) (m : M) :
    letI : Comodule K H N := Comodule.Transport e
    tangentOperator K d (e m) = e (tangentOperator K d m) := by
  let : Comodule K H N := Comodule.Transport e
  simp only [tangentOperator, LinearMap.comp_apply,
    Comodule.transport_coact_apply, LinearEquiv.symm_apply_apply]
  generalize Comodule.coact (R := K) (C := H) m = t
  induction t using TensorProduct.inductionOn with
  | tmul m h =>
    change Bialgebra.CounitAlgebra.algEquivSelf K H K (d h) • e m =
      e (Bialgebra.CounitAlgebra.algEquivSelf K H K (d h) • m)
    exact (map_smul e (Bialgebra.CounitAlgebra.algEquivSelf K H K (d h)) m).symm
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

private theorem block_coact_basis {k : ℕ} (n : Fin k → ℕ)
    (j : Σ i, Fin (n i + 1)) :
    letI := blockComodule K n
    Comodule.coact (R := K) (C := SpecialLinear.coordinateHopfAlgebra K 2)
        ((Pi.basisFun K (Σ i, Fin (n i + 1))) j) =
      ∑ i, (Pi.basisFun K (Σ i, Fin (n i + 1))) i ⊗ₜ[K] blockCoefficients K n i j := by
  let := blockComodule K n
  exact Comodule.matrixCoact_apply_basisFun K (blockCoefficients K n) j

private theorem block_tangent_basis {k : ℕ} (n : Fin k → ℕ)
    (d : Derivation K (SpecialLinear.coordinateHopfAlgebra K 2)
      (Bialgebra.CounitAlgebra K (SpecialLinear.coordinateHopfAlgebra K 2) K))
    (j : Σ i, Fin (n i + 1)) :
    letI := blockComodule K n
    tangentOperator K d ((Pi.basisFun K (Σ i, Fin (n i + 1))) j) =
      ∑ i, Bialgebra.CounitAlgebra.algEquivSelf K
        (SpecialLinear.coordinateHopfAlgebra K 2) K (d (blockCoefficients K n i j)) •
          (Pi.basisFun K (Σ i, Fin (n i + 1))) i := by
  let := blockComodule K n
  have hc := block_coact_basis K n j
  change (TensorProduct.rid K _) (TensorProduct.map LinearMap.id
    ((Bialgebra.CounitAlgebra.algEquivSelf K _ K).toLinearMap.comp d.toLinearMap)
      (Comodule.coact (R := K) (C := SpecialLinear.coordinateHopfAlgebra K 2)
        ((Pi.basisFun K (Σ i, Fin (n i + 1))) j))) = _
  rw [hc]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.comp_apply, TensorProduct.rid_tmul]
  rfl

private theorem coefficient_differential (n : ℕ)
    (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) (i j : Fin (n + 1)) :
    Bialgebra.CounitAlgebra.algEquivSelf K (SpecialLinear.coordinateHopfAlgebra K 2) K
        (((SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x)
          (((GeneralLinear.genericMatrix K (n + 1)).map (coordinateMap K n)) i j)) =
      LinearMap.toMatrix (Sl2Std.basis K n) (Sl2Std.basis K n) (Sl2Std.rep K n x) i j := by
  have h := congrFun (congrFun (coordinateMap_differential K n x) i) j
  rw [affineGroupMatrixDifferential_apply, GeneralLinear.tangentMatrix_apply,
    algEquivSelf_derivationComp_apply] at h
  exact h

private theorem block_tangent_matrix {k : ℕ} (n : Fin k → ℕ)
    (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    letI := blockComodule K n
    LinearMap.toMatrix (Pi.basisFun K (Σ i, Fin (n i + 1)))
        (Pi.basisFun K (Σ i, Fin (n i + 1)))
        (tangentOperator K
          ((SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x)) =
      Matrix.blockDiagonal' fun a => LinearMap.toMatrix
        (Sl2Std.basis K (n a)) (Sl2Std.basis K (n a)) (Sl2Std.rep K (n a) x) := by
  classical
  let := blockComodule K n
  apply Matrix.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, block_tangent_basis]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  by_cases hab : a = b
  · subst b
    rw [blockCoefficients, Matrix.blockDiagonal'_apply_eq,
      Matrix.blockDiagonal'_apply_eq]
    exact coefficient_differential K (n a) x i j
  · rw [blockCoefficients, Matrix.blockDiagonal'_apply_ne _ _ _ hab,
      Matrix.blockDiagonal'_apply_ne _ _ _ hab, map_zero, map_zero]

private theorem tangent_transport_matrix {H : Type*} [CommRing H] [Bialgebra K H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Comodule K H (ι → K)]
    {M : Type*} [AddCommGroup M] [Module K M] (b : Basis ι K M)
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) :
    letI : Comodule K H M := Comodule.Transport b.equivFun.symm
    LinearMap.toMatrix b b (tangentOperator K d) =
      LinearMap.toMatrix (Pi.basisFun K ι) (Pi.basisFun K ι) (tangentOperator K d) := by
  let : Comodule K H M := Comodule.Transport b.equivFun.symm
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr]
  have hb : b.equivFun.symm ((Pi.basisFun K ι) j) = b j := by
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext q
    simp [Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have ht := tangentOperator_transport K b.equivFun.symm d ((Pi.basisFun K ι) j)
  rw [hb] at ht
  have h := congrFun (congrArg b.equivFun ht) i
  simpa only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply] using h

private theorem derivative_coefficient {H : Type*} [CommRing H] [Bialgebra K H]
    {M : Type*} [AddCommGroup M] [Module K M] [Comodule K H M]
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) (φ : M →ₗ[K] K) (m : M) :
    φ (tangentOperator K d m) =
      Bialgebra.CounitAlgebra.algEquivSelf K H K
        (d (Comodule.matrixCoefficient (R := K) (C := H) φ m)) := by
  let f := (Bialgebra.CounitAlgebra.algEquivSelf K H K).toLinearMap.comp d.toLinearMap
  change φ ((TensorProduct.rid K M)
      (TensorProduct.map LinearMap.id f (Comodule.coact (R := K) (C := H) m))) =
    f ((TensorProduct.lid K H)
      (TensorProduct.map φ LinearMap.id (Comodule.coact (R := K) (C := H) m)))
  generalize Comodule.coact (R := K) (C := H) m = t
  induction t using TensorProduct.inductionOn with
  | tmul v h => simp [mul_comm]
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

private theorem coordinate_differential {H : Type*} [CommRing H] [HopfAlgebra K H]
    {M : Type*} [AddCommGroup M] [Module K M] [Comodule K H M]
    {m : ℕ} (b : Basis (Fin m) K M)
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) :
    affineGroupMatrixDifferential m (Comodule.coordinateBialgHom b) d =
      LinearMap.toMatrix b b (tangentOperator K d) := by
  apply Matrix.ext
  intro i j
  rw [affineGroupMatrixDifferential_apply, GeneralLinear.tangentMatrix_apply,
    algEquivSelf_derivationComp_apply]
  calc
    _ = Bialgebra.CounitAlgebra.algEquivSelf K H K
        (d (Comodule.matrixCoefficient (R := K) (C := H) (b.coord i) (b j))) :=
      congrArg (fun h : H => Bialgebra.CounitAlgebra.algEquivSelf K H K (d h))
        (Comodule.coordinateBialgHom_X b i j)
    _ = b.coord i (tangentOperator K d (b j)) :=
      (derivative_coefficient K d (b.coord i) (b j)).symm
    _ = _ := (LinearMap.toMatrix_apply b b (tangentOperator K d) i j).symm

section Decomposition

variable {M : Type v} [AddCommGroup M] [Module K M]
  [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) K) M]
  [LieModule K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M]

private def decompositionBasis {k : ℕ}
    (N : Fin k → LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M)
    (n : Fin k → ℕ) (hint : DirectSum.IsInternal fun i => (N i).toSubmodule)
    (e : ∀ i, N i ≃ₗ⁅K,LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K (n i)) :
    Basis (Σ i, Fin (n i + 1)) K M :=
  hint.collectedBasis fun i => (Sl2Std.basis K (n i)).map (e i).symm.toLinearEquiv

private theorem decomposition_action_matrix {k : ℕ}
    (N : Fin k → LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M)
    (n : Fin k → ℕ) (hint : DirectSum.IsInternal fun i => (N i).toSubmodule)
    (e : ∀ i, N i ≃ₗ⁅K,LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K (n i))
    (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    LinearMap.toMatrix (decompositionBasis K N n hint e) (decompositionBasis K N n hint e)
        (LieModule.toEnd K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M x) =
      Matrix.blockDiagonal' fun a => LinearMap.toMatrix
        (Sl2Std.basis K (n a)) (Sl2Std.basis K (n a)) (Sl2Std.rep K (n a) x) := by
  classical
  let bs := fun i => (Sl2Std.basis K (n i)).map (e i).symm.toLinearEquiv
  apply Matrix.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  rw [LinearMap.toMatrix_apply]
  change (hint.collectedBasis bs).repr ⁅x, (hint.collectedBasis bs) ⟨b, j⟩⁆ ⟨a, i⟩ = _
  rw [hint.collectedBasis_coe]
  have hm : ⁅x, (bs b j : M)⁆ ∈ (N b).toSubmodule := (N b).lie_mem (bs b j).property
  by_cases hab : a = b
  · subst b
    rw [hint.collectedBasis_repr_of_mem bs hm, Matrix.blockDiagonal'_apply_eq,
      LinearMap.toMatrix_apply]
    change (Sl2Std.basis K (n a)).repr
        ((e a) ⁅x, (e a).symm (Sl2Std.basis K (n a) j)⁆) i = _
    have he : (e a) ⁅x, (e a).symm (Sl2Std.basis K (n a) j)⁆ =
        ⁅x, (e a) ((e a).symm (Sl2Std.basis K (n a) j))⁆ := (e a).map_lie'
    rw [he, LieModuleEquiv.apply_symm_apply, Sl2Std.lie_eq_rep_apply]
  · rw [hint.collectedBasis_repr_of_mem_ne bs (Ne.symm hab) hm,
      Matrix.blockDiagonal'_apply_ne _ _ _ hab]

end Decomposition

variable [CharZero K] [IsAlgClosed K]

/-- Every finite-dimensional `sl₂` representation is the differential of an algebraic one. -/
theorem exists_coordinateMap_differential {M : Type v} [AddCommGroup M] [Module K M]
    [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin 2) K) M]
    [LieModule K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M]
    [FiniteDimensional K M] {m : ℕ} (b : Basis (Fin m) K M) :
    ∃ φ : GeneralLinear.coordinateHopfAlgebra K m →ₐc[K]
        SpecialLinear.coordinateHopfAlgebra K 2,
      ∀ x : LieAlgebra.SpecialLinear.sl (Fin 2) K,
        affineGroupMatrixDifferential m φ
            ((SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) =
          LinearMap.toMatrix b b
            (LieModule.toEnd K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M x) := by
  classical
  obtain ⟨k, N, n, hint, he⟩ := Sl2Std.exists_isInternal_lieModuleEquiv K M
  let e : ∀ i, N i ≃ₗ⁅K,LieAlgebra.SpecialLinear.sl (Fin 2) K⁆ Sl2Std K (n i) :=
    fun i => (he i).some
  let c := decompositionBasis K N n hint e
  let : Comodule K (SpecialLinear.coordinateHopfAlgebra K 2)
      ((Σ i, Fin (n i + 1)) → K) := blockComodule K n
  let : Comodule K (SpecialLinear.coordinateHopfAlgebra K 2) M :=
    Comodule.Transport c.equivFun.symm
  have hop (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
      tangentOperator K ((SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) =
        LieModule.toEnd K (LieAlgebra.SpecialLinear.sl (Fin 2) K) M x := by
    apply (LinearMap.toMatrix c c).injective
    rw [tangent_transport_matrix, block_tangent_matrix,
      decomposition_action_matrix K N n hint e x]
  refine ⟨Comodule.coordinateBialgHom b, fun x => ?_⟩
  rw [coordinate_differential, hop]

end ReductiveGroups.BinaryForms
