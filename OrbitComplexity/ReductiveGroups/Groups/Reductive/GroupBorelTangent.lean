import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupUnipotent
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotentKernel
import OrbitComplexity.ReductiveGroups.Groups.Representations.ConjugateSubgroupTangent

/-!
# The torus and unipotent decomposition of a Borel tangent algebra

The tangent algebra of a Borel subgroup is the direct sum, as a vector space,
of the maximal torus tangent and the tangent of its root-unipotent subgroup.
The proof decomposes the Borel tangent into its Cartan weight spaces.

## Main results

* `ReductiveGroups.ReductiveGroupData.borelTangent_eq_sup`: the vector-space sum.
* `ReductiveGroups.ReductiveGroupData.torus_disjoint_unipotent`: disjoint summands.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti LieAlgebra LieModule

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The tangent image in the group tangent algebra of a closed subgroup. -/
abbrev subgroupTangent (I : HopfIdeal K G.coordinateAlgebra) : LieSubalgebra K G.tangent :=
  hopfTangentImage I

/-- The tangent Lie algebra of the chosen Borel subgroup, inside the group tangent algebra. -/
abbrev borelTangent : LieSubalgebra K G.tangent := G.subgroupTangent G.borelIdeal

/-- The tangent Lie algebra of the chosen root-unipotent subgroup. -/
abbrev unipotentTangent : LieSubalgebra K G.tangent := G.subgroupTangent G.unipotentIdeal

omit [IsAlgClosed K] [CharZero K] in
/-- The maximal torus tangent is contained in the Borel tangent. -/
theorem torusTangent_le_borel : G.torusTangent ≤ G.borelTangent :=
  TorusUnipotent.torusTangentImage_le_borelTangentImage G.torusIdeal G.borelIdeal G.borel_le_torus
    G.torusSplit G.split_eq_zero

/-- The root-unipotent tangent is contained in the Borel tangent. -/
theorem unipotentTangent_le_borel : G.unipotentTangent ≤ G.borelTangent :=
  hopfQuotient_tangentImage_antitone G.unipotentIdeal G.borelIdeal G.borel_le_unipotentIdeal

/-- A root-character subspace lies in the Borel tangent exactly when the root is positive. -/
theorem rootWeightSpace_le_borel (r : G.rootIndex) :
    G.rootWeightSpace r ≤ G.borelTangent.toSubmodule ↔ G.rootBase.IsPos r := by
  have h := borelRootBase_isPos_iff G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm r)
  change G.rootBase.IsPos (G.characterRootEquiv (G.characterRootEquiv.symm r)) ↔
    G.rootWeightSpace r ≤ G.borelTangent.toSubmodule at h
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- A negative root-character subspace has zero intersection with the Borel tangent. -/
theorem rootWeightSpace_inf_borel (r : G.rootIndex) (hr : ¬ G.rootBase.IsPos r) :
    G.rootWeightSpace r ⊓ G.borelTangent.toSubmodule = ⊥ := by
  by_contra hne
  let i : borelRootCharacterIndex G.borelIdeal G.torusSplit :=
    ⟨G.rootCharacter r, G.rootCharacter_ne_one r, by
      change G.borelTangent.toSubmodule ⊓ G.rootWeightSpace r ≠ ⊥
      simpa only [inf_comm] using hne⟩
  have hi := borelRootBase_isPos G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive i
  have he : borelRootCharacterOccurring G.borelIdeal G.torusSplit i =
      G.characterRootEquiv.symm r := by
    apply Subtype.ext
    rfl
  rw [he] at hi
  change G.rootBase.IsPos (G.characterRootEquiv (G.characterRootEquiv.symm r)) at hi
  exact hr (by simpa only [Equiv.apply_symm_apply] using hi)

/-- The unipotent tangent is the sum of the nonidentity character parts of the Borel tangent. -/
theorem unipotentTangent_eq_character_sum : G.unipotentTangent.toSubmodule =
    ⨆ (α : G.characters) (_ : α ≠ 1),
      G.borelTangent.toSubmodule ⊓ affineGroupCharacterWeightSpace G.torusSplit α :=
  BorelRootUnipotentTangent.eq_character_sum G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- Every positive root-character subspace lies in the unipotent tangent. -/
theorem rootWeightSpace_le_unipotent (r : G.rootIndex) (hr : G.rootBase.IsPos r) :
    G.rootWeightSpace r ≤ G.unipotentTangent.toSubmodule := by
  rw [G.unipotentTangent_eq_character_sum]
  exact le_iSup₂_of_le (G.rootCharacter r) (G.rootCharacter_ne_one r)
    (le_inf ((G.rootWeightSpace_le_borel r).mpr hr) le_rfl)

/-- The root-unipotent tangent is exactly the sum of the positive root-character subspaces. -/
theorem unipotentTangent_eq_iSup_pos : G.unipotentTangent.toSubmodule =
    ⨆ (r : G.rootIndex) (_ : G.rootBase.IsPos r), G.rootWeightSpace r := by
  apply le_antisymm
  · rw [G.unipotentTangent_eq_character_sum]
    refine iSup₂_le fun α hα => ?_
    by_cases hW : affineGroupCharacterWeightSpace G.torusSplit α = ⊥
    · simp only [hW, inf_bot_eq]
      exact bot_le
    · let a : {α : G.characters //
          affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ ∧ α ≠ 1} := ⟨α, hW, hα⟩
      let r := G.characterRootEquiv a
      have he : G.rootCharacter r = α := by
        change (G.characterRootEquiv.symm (G.characterRootEquiv a)).val = α
        rw [Equiv.symm_apply_apply]
      by_cases hr : G.rootBase.IsPos r
      · rw [← he]
        exact le_iSup₂_of_le r hr inf_le_right
      · have hz : G.borelTangent.toSubmodule ⊓
            affineGroupCharacterWeightSpace G.torusSplit α = ⊥ := by
          simpa only [rootWeightSpace, he, inf_comm] using G.rootWeightSpace_inf_borel r hr
        rw [hz]
        exact bot_le
  · exact iSup₂_le fun r hr => G.rootWeightSpace_le_unipotent r hr

/-- The Borel tangent is the sum of the torus tangent and the root-unipotent tangent. -/
theorem borelTangent_eq_sup : G.borelTangent.toSubmodule =
    G.torusTangent.toSubmodule ⊔ G.unipotentTangent.toSubmodule := by
  apply le_antisymm
  · exact TorusUnipotent.BorelTangent.le_torus_sup_borelRootUnipotentTangent
      G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
      G.torusSplit G.split_surjective G.split_eq_zero G.reductive
  · exact sup_le G.torusTangent_le_borel G.unipotentTangent_le_borel

/-- The torus and root-unipotent tangent subspaces have zero intersection. -/
theorem torus_disjoint_unipotent :
    Disjoint G.torusTangent.toSubmodule G.unipotentTangent.toSubmodule := by
  rw [disjoint_iff]
  have h := BorelRootUnipotentTangent.inf_torus_eq_bot G.borelIdeal G.isBorel
    G.torusSplit G.split_surjective
  have he := congrArg LieSubalgebra.toSubmodule h
  rw [LieSubalgebra.inf_toSubmodule, LieSubalgebra.bot_toSubmodule] at he
  change G.unipotentTangent.toSubmodule ⊓ G.torusTangent.toSubmodule = ⊥ at he
  simpa only [inf_comm] using he

end ReductiveGroupData
