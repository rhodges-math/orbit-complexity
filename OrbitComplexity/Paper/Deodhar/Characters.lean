import OrbitComplexity.Paper.Deodhar.RootActions
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositiveCharacter
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Batteries.Tactic.Lint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.GroupActions.Tori.RealSpanRank

/-! # Root characters and real coordinate spans

Root characters embed the integral root lattice into the torus character lattice. Passing
both coordinate families to the reals preserves their span dimensions.

## Main results

* `rootCharacter_real_rank`: equality of character and simple-coordinate real span dimensions.
* `rootCharacter_root_rank`: equality with the normalized real-root span dimension.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups
universe u v
private theorem spanRank_map {R : Type*} [Ring R] {ι : Type v} {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) (v : ι → A) :
    Module.finrank R (Submodule.span R (Set.range (fun i => f (v i)))) =
      Module.finrank R (Submodule.span R (Set.range v)) := by
  have hm : (Submodule.span R (Set.range v)).map f =
      Submodule.span R (Set.range (fun i => f (v i))) := by
    rw [Submodule.map_span]
    congr 1
    exact (Set.range_comp' f v).symm
  rw [← hm]
  exact congrArg Cardinal.toNat (rank_map_eq hf _)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

set_option maxHeartbeats 400000 in
/-- Root characters and integral simple-root coordinates have equal real span dimension. -/
theorem rootCharacter_real_rank {ι : Type v} (roots : ι → G.rootIndex) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (i : ι) (k : G.torusIndex) => ((G.rootCharacter (roots i)).toAdd k : ℝ)))) =
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (i : ι) (j : G.rootBase.support) => ((G.rootBase.toWeightBasisInt.repr
        (G.rootSystem.rootSpanMem ℤ (roots i))) j : ℝ)))) := by
  rw [GroupActions.finrank_realSpan_finsupp, GroupActions.finrank_realSpan_finsupp]
  have hchar := spanRank_map (R := ℤ) (ι := ι)
    G.rootCharacterMap G.rootCharacterMap_injective
    (fun i : ι => G.rootSystem.rootSpanMem ℤ (roots i))
  have him : (fun i => G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ (roots i))) =
      (fun i => (G.rootCharacter (roots i)).toAdd) :=
    funext (fun i => G.rootCharacterMap_root (roots i))
  rw [him] at hchar
  let e : G.rootSystem.rootSpan ℤ ≃ₗ[ℤ] (G.rootBase.support →₀ ℤ) :=
    G.rootBase.toWeightBasisInt.repr
  have hcoord := spanRank_map (R := ℤ) (ι := ι) e.toLinearMap e.injective
    (fun i : ι => G.rootSystem.rootSpanMem ℤ (roots i))
  exact hchar.trans hcoord.symm

private theorem span_rescale {ι : Type v} {V : Type u} [AddCommGroup V] [Module ℝ V]
    (vectors : ι → V) (scalars : ι → ℝ) (hne : ∀ i, scalars i ≠ 0) :
    Submodule.span ℝ (Set.range (fun i => scalars i • vectors i)) =
      Submodule.span ℝ (Set.range vectors) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℝ (Set.range (fun i => scalars i • vectors i))) (scalars i)⁻¹
      (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [smul_smul, inv_mul_cancel₀ (hne i), one_smul, SetLike.mem_coe] using h

set_option maxHeartbeats 400000 in
/-- Root characters have the real span dimension of their normalized root coordinates. -/
theorem rootCharacter_normalized_rank {ι : Type v} (roots : ι → G.rootIndex) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (i : ι) (k : G.torusIndex) => ((G.rootCharacter (roots i)).toAdd k : ℝ)))) =
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun (i : ι) =>
      (Real.sqrt ((G.rootSystem.posRootForm ℤ).rootLength (roots i) : ℝ))⁻¹ •
        (fun (j : G.rootBase.support) => ((G.rootBase.toWeightBasisInt.repr
          (G.rootSystem.rootSpanMem ℤ (roots i))) j : ℝ))))) := by
  rw [rootCharacter_real_rank]
  have hpos (i : ι) :
      0 < ((G.rootSystem.posRootForm ℤ).rootLength (roots i) : ℝ) := by
    exact_mod_cast (G.rootSystem.posRootForm ℤ).rootLength_pos (roots i)
  have he := span_rescale
    (fun (i : ι) (j : G.rootBase.support) => ((G.rootBase.toWeightBasisInt.repr
      (G.rootSystem.rootSpanMem ℤ (roots i))) j : ℝ))
    (fun i => (Real.sqrt ((G.rootSystem.posRootForm ℤ).rootLength (roots i) : ℝ))⁻¹)
    (fun i => inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (hpos i))))
  exact (congrArg (fun p : Submodule ℝ (G.rootBase.support → ℝ) =>
    Module.finrank ℝ p) he).symm

private theorem real_span_coe {ι κ : Type*} [Finite κ] (vectors : ι → κ →₀ ℝ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i k => vectors i k))) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range vectors)) := by
  let e := Finsupp.linearEquivFunOnFinite ℝ ℝ κ
  have h := e.finrank_map_eq (Submodule.span ℝ (Set.range vectors))
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h


set_option maxHeartbeats 400000 in
/-- Torus root characters and normalized real roots have the same span dimension. -/
theorem rootCharacter_root_rank {ι : Type*} (roots : ι → G.rootIndex) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (i : ι) (k : G.torusIndex) => ((G.rootCharacter (roots i)).toAdd k : ℝ)))) =
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i => normalizedRoot G.rootBase (roots i)))) := by
  rw [rootCharacter_normalized_rank]
  have h := real_span_coe (fun i : ι => normalizedRoot G.rootBase (roots i))
  have hv : (fun (i : ι) (j : G.rootBase.support) =>
      normalizedRoot G.rootBase (roots i) j) =
      (fun i : ι =>
        (Real.sqrt ((G.rootSystem.posRootForm ℤ).rootLength (roots i) : ℝ))⁻¹ •
          (fun j : G.rootBase.support => ((G.rootBase.toWeightBasisInt.repr
            (G.rootSystem.rootSpanMem ℤ (roots i))) j : ℝ))) := by
    funext i j
    rw [normalizedRoot_apply]
    rfl
  rw [hv] at h
  exact h


section RealCharacters
attribute [local instance] Classical.propDecidable

/-- Real simple-root coordinates map to the real character coordinates of the torus. -/
def realCharacterMap : (G.rootBase.support →₀ ℝ) →ₗ[ℝ] (G.torusIndex → ℝ) :=
  Finsupp.linearCombination ℝ
    (fun i : G.rootBase.support => fun j => ((G.rootCharacter i).toAdd j : ℝ))

/-- The real character map carries each real root to its root character. -/
theorem realCharacterMap_root (r : G.rootIndex) :
    realCharacterMap G (realRoot G.rootBase r) =
      (fun j => ((G.rootCharacter r).toAdd j : ℝ)) := by
  classical
  let := Fintype.ofFinite G.rootBase.support
  have hz : (∑ i : G.rootBase.support,
      G.rootBase.toWeightBasisInt.repr (G.rootSystem.rootSpanMem ℤ r) i •
        (G.rootCharacter i).toAdd) = (G.rootCharacter r).toAdd := by
    rw [← G.rootCharacterMap_root r]
    exact (G.rootBase.toWeightBasisInt.constr_apply_fintype ℤ
      (fun i => (G.rootCharacter i).toAdd) (G.rootSystem.rootSpanMem ℤ r)).symm
  ext j
  have hj := congrArg (fun x : G.torusIndex →₀ ℤ => x j) hz
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hj
  change ((Finsupp.linearCombination ℝ
    (fun i : G.rootBase.support => fun j => ((G.rootCharacter i).toAdd j : ℝ)))
      (realRoot G.rootBase r)) j = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRoot_apply]
    exact_mod_cast hj
  · intro i
    exact zero_smul ℝ _

/-- The real character map is injective, including when the group has a central torus. -/
theorem realCharacterMap_injective : Function.Injective (realCharacterMap G) := by
  classical
  let := Fintype.ofFinite G.rootBase.support
  have hreal : LinearIndependent ℝ
      (fun i : G.rootBase.support => fun j => ((G.rootCharacter i).toAdd j : ℝ)) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card G.rootBase.support = Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun i : G.rootBase.support =>
        fun j => ((G.rootCharacter i).toAdd j : ℝ))))
    exact ((GroupActions.finrank_realSpan_finsupp
      (fun i : G.rootBase.support => (G.rootCharacter i).toAdd)).trans
        (finrank_span_eq_card G.rootCharacter_independent)).symm
  exact hreal.finsuppLinearCombination_injective

/-- Twice rho maps to the character of the Borel determinant line. -/
theorem realCharacterMap_twoRho :
    realCharacterMap G (realTwoRho G.rootBase) =
      (fun j => (G.positiveRootCharacter.toAdd j : ℝ)) := by
  classical
  simp only [realTwoRho, map_sum, realCharacterMap_root,
    ReductiveGroups.ReductiveGroupData.positiveRootCharacter, toAdd_prod]
  ext j
  simp only [Finset.sum_apply, Finsupp.finsetSum_apply, Int.cast_sum]
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro r hr
    rfl

/-- Weyl translates of twice rho map to the corresponding sums of root characters. -/
theorem realCharacterMap_weyl_twoRho (w : G.weylGroup) :
    realCharacterMap G (rootCoordinateAction G.rootBase w (realTwoRho G.rootBase)) =
      (fun j => (((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
        G.rootCharacter (G.rootSystem.weylGroupToPerm w r)).toAdd) j : ℝ)) := by
  classical
  simp only [realTwoRho, map_sum, rootCoordinateAction_root, realCharacterMap_root,
    toAdd_prod]
  ext j
  simp only [Finset.sum_apply, Finsupp.finsetSum_apply, Int.cast_sum]


end RealCharacters

end SchubertOrbits
