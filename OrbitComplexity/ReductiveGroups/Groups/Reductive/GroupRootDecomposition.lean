import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusZeroWeight

/-!
# The torus and root subspaces of a reductive group tangent algebra

The identity character space is the maximal torus tangent. Every other nonzero
character space is indexed by a root of the center quotient. Together they span
the original tangent algebra.

## Main results

* `ReductiveGroups.ReductiveGroupData.tangent_eq_torus_sup_roots`: the complete root sum.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The identity character space is exactly the maximal torus tangent. -/
theorem identityWeightSpace_eq_torus :
    affineGroupCharacterWeightSpace G.torusSplit 1 = G.torusTangent.toSubmodule :=
  (torusTangent_isCartan_iff_identityWeight G.torusSplit G.split_surjective).mp inferInstance

/-- Distinct roots have distinct torus characters. -/
theorem rootCharacter_injective : Function.Injective G.rootCharacter := by
  intro r s h
  apply G.characterRootEquiv.symm.injective
  exact Subtype.ext h

/-- The maximal torus tangent and all root-character subspaces span the group tangent algebra. -/
theorem tangent_eq_torus_sup_roots :
    G.torusTangent.toSubmodule ⊔ (⨆ r : G.rootIndex, G.rootWeightSpace r) = ⊤ := by
  apply top_unique
  rw [← ISup.affineGroupCharacterWeightSpace_eq_top G.torusSplit]
  refine iSup_le fun α => ?_
  by_cases hα : α = 1
  · rw [hα, G.identityWeightSpace_eq_torus]
    exact le_sup_left
  · by_cases hW : affineGroupCharacterWeightSpace G.torusSplit α = ⊥
    · rw [hW]
      exact bot_le
    · let a : {α : G.characters //
          affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ ∧ α ≠ 1} := ⟨α, hW, hα⟩
      have he : G.rootCharacter (G.characterRootEquiv a) = α := by
        change (G.characterRootEquiv.symm (G.characterRootEquiv a)).val = α
        rw [Equiv.symm_apply_apply]
      rw [← he]
      exact le_sup_of_le_right (le_iSup G.rootWeightSpace (G.characterRootEquiv a))

/-- The longest Weyl element reverses the signs of all roots of the chosen group. -/
theorem longestElement_isPos_iff (r : G.rootIndex) :
    G.rootBase.IsPos (G.rootSystem.weylGroupToPerm G.longestElement r) ↔
      ¬ G.rootBase.IsPos r :=
  longestWeylElement_isPos_iff G.rootBase r

/-- Acting twice by the longest Weyl element fixes every root. -/
theorem longestElement_root_involutive :
    Function.Involutive (G.rootSystem.weylGroupToPerm G.longestElement) := by
  intro r
  change (G.rootSystem.weylGroupToPerm G.longestElement *
    G.rootSystem.weylGroupToPerm G.longestElement) r = r
  rw [← map_mul]
  change (G.rootSystem.weylGroupToPerm
    (longestWeylElement G.rootBase * longestWeylElement G.rootBase)) r = r
  rw [longestWeylElement_sq, map_one]
  rfl

end ReductiveGroupData
