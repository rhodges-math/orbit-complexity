import OrbitComplexity.ReductiveGroups.GLn.GroupData
import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularIdeal
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification
import Mathlib.Tactic

/-! # Matrix roots and root parameters -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open scoped Classical

noncomputable section
namespace ReductiveGroups.GLn
universe u
variable {K : Type u} [Field K] (n : ℕ)

private theorem kills_upperIdeal_iff
    (d : Derivation K (coordinateHopfAlgebra K n)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K n) K)) :
    (∀ a ∈ GLn.upperTriangularIdeal K n, d a = 0) ↔
      ∀ i j : Fin n, j < i → d (genericMatrix K n i j) = 0 := by
  constructor
  · intro h i j hij
    exact h _ (GLn.genericMatrix_mem_upperTriangularIdeal hij)
  · intro h a ha
    rw [← HopfIdeal.mem_toIdeal, GLn.upperTriangularIdeal_toIdeal] at ha
    refine Submodule.span_induction (p := fun a _ => d a = 0) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨i, j, hij, rfl⟩
      exact h i j hij
    · exact map_zero d
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x hx hd
      change d (r * x) = 0
      rw [d.leibniz, hd, smul_zero, zero_add]
      apply (Bialgebra.CounitAlgebra.algEquivSelf K (coordinateHopfAlgebra K n) K).injective
      rw [Bialgebra.CounitAlgebra.algEquivSelf_smul, map_zero]
      have hxI : x ∈ GLn.upperTriangularIdeal K n := by
        rw [← HopfIdeal.mem_toIdeal, GLn.upperTriangularIdeal_toIdeal]
        exact hx
      simp only [(GLn.upperTriangularIdeal K n).counit_eq_zero hxI, map_zero, zero_mul]

/-- A tangent of the upper triangular subgroup has an upper triangular tangent matrix. -/

private theorem tangent_upper_iff
    (d : Derivation K (coordinateHopfAlgebra K n)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K n) K)) :
    d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K (coordinateHopfAlgebra K n))
        (GLn.upperTriangularIdeal K n)).hom).range ↔
      (tangentMatrix n d).IsUpperTriangular := by
  let q := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K (coordinateHopfAlgebra K n))
    (GLn.upperTriangularIdeal K n)).hom
  rw [tangent_mem_range_iff_kills_kernel q Ideal.Quotient.mk_surjective]
  have hker (a : coordinateHopfAlgebra K n) :
      q a = 0 ↔ a ∈ GLn.upperTriangularIdeal K n := by
    change Ideal.Quotient.mk (GLn.upperTriangularIdeal K n).toIdeal a = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, HopfIdeal.mem_toIdeal]
  simp_rw [hker]
  rw [kills_upperIdeal_iff]
  constructor
  · intro h i j hij
    change (Bialgebra.CounitAlgebra.algEquivSelf K (coordinateHopfAlgebra K n) K)
      (d (genericMatrix K n i j)) = 0
    rw [h i j hij, map_zero]
  · intro h i j hij
    apply (Bialgebra.CounitAlgebra.algEquivSelf K (coordinateHopfAlgebra K n) K).injective
    rw [map_zero]
    exact h hij

variable [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_map_eq : GLn.torusRestriction K n =
    (TauCeti.GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n)).hom := by
  have h : (GLn.torusRestriction K n).toAlgHom =
      (TauCeti.GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n)).hom.toAlgHom := by
    apply coordinateHopfAlgebra_algHom_ext K n
    intro i j
    exact (ReductiveGroups.diagonalTorusCoordinateMap_X (R := K) (N := n) i j).trans
      (TauCeti.GeneralLinear.diagonalTorusCoordinateMap_X (R := K) (N := n) i j).symm
  exact BialgHom.coe_toAlgHom_injective h

omit [IsAlgClosed K] [CharZero K] in
private theorem matrix_weight_ne_bot (i j : Fin n) :
    affineGroupCharacterWeightSpace (GLn.torusRestriction K n) (matrixUnitWeight i j) ≠ ⊥ := by
  rw [torus_map_eq]
  let e := Derivation.cotangentLinearEquiv
    (R := K) (A := coordinateHopfAlgebra K n) (B := K)
  refine (Submodule.ne_bot_iff _).mpr ⟨e (matrixUnitTangent i j), ?_, ?_⟩
  · change e.symm (e (matrixUnitTangent i j)) ∈ Derivation.adjointWeightSpace
      (TauCeti.GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n)).hom (matrixUnitWeight i
        j)
    rw [e.symm_apply_apply]
    exact matrixUnitTangent_mem_adjointWeightSpace i j
  · exact e.map_ne_zero_iff.mpr (matrixUnitTangent_ne_zero i j)

/-- The general-linear root with character tᵢtⱼ⁻¹. -/
def matrixRoot (i j : Fin n) (hij : i ≠ j) : (GLn.groupData K n).rootIndex :=
  (GLn.groupData K n).characterRootEquiv ⟨matrixUnitWeight i j,
    matrix_weight_ne_bot n i j, (matrixUnitWeight_eq_one_iff i j).not.mpr hij⟩

/-- The character of a matrix root is the corresponding diagonal ratio. -/
theorem rootCharacter_matrixRoot (i j : Fin n) (hij : i ≠ j) :
    (GLn.groupData K n).rootCharacter (matrixRoot n i j hij) = matrixUnitWeight i j := by
  change ((GLn.groupData K n).characterRootEquiv.symm
    ((GLn.groupData K n).characterRootEquiv _)).val = _
  rw [Equiv.symm_apply_apply]

/-- Every general-linear root character is a diagonal ratio with distinct indices. -/
theorem rootCharacter_pair (r : (GLn.groupData K n).rootIndex) :
    ∃ i j : Fin n, i ≠ j ∧ (GLn.groupData K n).rootCharacter r = matrixUnitWeight i j := by
  let G := GLn.groupData K n
  let e := Derivation.cotangentLinearEquiv
    (R := K) (A := coordinateHopfAlgebra K n) (B := K)
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp (G.rootWeightSpace_ne_bot r)
  change e.symm d ∈ Derivation.adjointWeightSpace (GLn.torusRestriction K n)
    (G.rootCharacter r) at hd
  rw [torus_map_eq] at hd
  have hspace : Derivation.adjointWeightSpace
      (TauCeti.GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n)).hom (G.rootCharacter r) ≠
        ⊥ := by
    refine (Submodule.ne_bot_iff _).mpr ⟨e.symm d, hd, ?_⟩
    exact e.symm.map_ne_zero_iff.mpr hd0
  apply (mem_nontrivialAdjointWeights_diagonalTorus_iff (k := K) (G.rootCharacter r)).mp
  exact ⟨G.rootCharacter_ne_one r, hspace⟩

private theorem matrix_unit_mem_root_weight (i j : Fin n) (hij : i ≠ j) :
    Derivation.cotangentLinearEquiv
      (R := K) (A := coordinateHopfAlgebra K n) (B := K) (matrixUnitTangent i j) ∈
      (GLn.groupData K n).rootWeightSpace (matrixRoot n i j hij) := by
  let e := Derivation.cotangentLinearEquiv
    (R := K) (A := coordinateHopfAlgebra K n) (B := K)
  change e.symm (e (matrixUnitTangent i j)) ∈ Derivation.adjointWeightSpace
    (GLn.torusRestriction K n) ((GLn.groupData K n).rootCharacter (matrixRoot n i j hij))
  rw [rootCharacter_matrixRoot, torus_map_eq, e.symm_apply_apply]
  exact matrixUnitTangent_mem_adjointWeightSpace i j

private theorem matrix_root_tangent (i j : Fin n) (hij : i ≠ j)
    (d : (GLn.groupData K n).tangent)
    (hd : d ∈ (GLn.groupData K n).rootWeightSpace (matrixRoot n i j hij)) :
    ∃ a : K, tangentMatrix n d = a • Matrix.single i j 1 := by
  let e := Derivation.cotangentLinearEquiv
    (R := K) (A := coordinateHopfAlgebra K n) (B := K)
  change e.symm d ∈ Derivation.adjointWeightSpace (GLn.torusRestriction K n)
    ((GLn.groupData K n).rootCharacter (matrixRoot n i j hij)) at hd
  rw [rootCharacter_matrixRoot, torus_map_eq,
    adjointWeightSpace_matrixUnitWeight_eq_span_singleton hij] at hd
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hd
  refine ⟨a, ?_⟩
  have hm := congrArg (cotangentDualMatrixEquiv (k := K) (n := n)) ha
  rw [map_smul, cotangentDualMatrixEquiv_matrixUnitTangent,
    cotangentDualMatrixEquiv_apply] at hm
  have hm' : tangentMatrix n (e (e.symm d)) = a • Matrix.single i j 1 := hm.symm
  exact (congrArg (tangentMatrix n) (e.apply_symm_apply d)).symm.trans hm'

/-- A matrix root is positive exactly when its row precedes its column. -/
theorem matrixRoot_positive (i j : Fin n) (hij : i ≠ j) :
    (GLn.groupData K n).rootBase.IsPos (matrixRoot n i j hij) ↔ i < j := by
  rw [← (GLn.groupData K n).rootWeightSpace_le_borel]
  constructor
  · intro hle
    let e := Derivation.cotangentLinearEquiv
      (R := K) (A := coordinateHopfAlgebra K n) (B := K)
    have hu := (tangent_upper_iff n
      (e (matrixUnitTangent i j))).mp (hle (matrix_unit_mem_root_weight n i j hij))
    have hm : tangentMatrix n (e (matrixUnitTangent i j)) = Matrix.single i j 1 :=
      (cotangentDualMatrixEquiv_apply (matrixUnitTangent i j)).symm.trans
        (cotangentDualMatrixEquiv_matrixUnitTangent i j)
    rw [hm] at hu
    by_contra hnot
    have hji : j < i := by omega
    have hc := hu hji
    exact one_ne_zero (by simpa only [Matrix.single_apply_same] using hc)
  · intro hpos d hd
    apply (tangent_upper_iff n d).mpr
    obtain ⟨a, ha⟩ := matrix_root_tangent n i j hij d hd
    rw [ha]
    intro r s hrs
    rw [Matrix.smul_apply, smul_eq_mul]
    have hz : (Matrix.single i j (1 : K)) r s = 0 := by
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hpos hrs
    rw [hz, mul_zero]

private theorem matrixWeight_toAdd (i j : Fin n) :
    (matrixUnitWeight.{u} i j).toAdd =
      Finsupp.single (ULift.up i) (1 : ℤ) - Finsupp.single (ULift.up j) 1 := rfl

omit [IsAlgClosed K] in
private theorem exp_single (i j : Fin n) (hij : i ≠ j) (a : K) :
    associativeExponential (K := K) (a • Matrix.single i j (1 : K)) =
      1 + a • Matrix.single i j (1 : K) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom _ (algebraMap ℚ K)
  have hs : (a • Matrix.single i j (1 : K)) ^ 2 = 0 := by
    rw [pow_two, smul_mul_assoc, mul_smul_comm,
      Matrix.single_mul_single_of_ne (1 : K) i j i hij.symm (1 : K), smul_zero, smul_zero]
  change IsNilpotent.exp (a • Matrix.single i j (1 : K)) = _
  rw [IsNilpotent.exp_eq_sum hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, one_smul]

omit [IsAlgClosed K] in
private theorem ga_scalar_matrix (i j : Fin n) (hij : i ≠ j)
    (φ : coordinateHopfAlgebra K n →ₐc[K] SymmetricAlgebra K K)
    (a : K) (ha : tangentMatrix n (gaAffineGroupTangent φ) = a • Matrix.single i j (1 : K))
    (t : K) :
    (pointsMulEquiv n (gaParameterPoint φ t) : Matrix (Fin n) (Fin n) K) =
      1 + (t * a) • Matrix.single i j 1 := by
  change (gaMatrixPoints n φ (Multiplicative.ofAdd t) : Matrix (Fin n) (Fin n) K) = _
  rw [GaMatrixPoints.eq_exponential_differential]
  change associativeExponential (K := K) (t • tangentMatrix n (gaAffineGroupTangent φ)) = _
  rw [ha, smul_smul, exp_single n i j hij]

/-- A root-parameter map has one off-diagonal matrix entry with nonzero coefficient. -/
theorem rootMap_matrix (i j : Fin n) (hij : i ≠ j)
    (φ : coordinateHopfAlgebra K n →ₐc[K] SymmetricAlgebra K K)
    (hφ : gaAffineGroupTangent φ ∈
      (GLn.groupData K n).rootWeightSpace (matrixRoot n i j hij))
    (hφ0 : gaAffineGroupTangent φ ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∀ t : K,
      (pointsMulEquiv n (gaParameterPoint φ t) : Matrix (Fin n) (Fin n) K) =
        1 + (t * a) • Matrix.single i j 1 := by
  obtain ⟨a, ha⟩ := matrix_root_tangent n i j hij (gaAffineGroupTangent φ) hφ
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hφ0
    apply (tangentLinearEquivMatrix n).injective
    change tangentMatrix n (gaAffineGroupTangent φ) = tangentMatrix n 0
    have hz : tangentMatrix n (gaAffineGroupTangent φ) = 0 :=
      ha.trans (by rw [hzero, zero_smul])
    exact hz.trans (map_zero (tangentMatrix n)).symm
  exact ⟨a, ha0, ga_scalar_matrix n i j hij φ a ha⟩

end ReductiveGroups.GLn
