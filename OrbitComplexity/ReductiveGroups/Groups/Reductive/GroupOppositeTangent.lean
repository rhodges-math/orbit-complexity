import OrbitComplexity.ReductiveGroups.Groups.Characters.WeightIndependence
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOpposite
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootDecomposition

/-!
# Complementary tangents of an opposite unipotent subgroup and a Borel subgroup

Conjugation by the longest Weyl representative sends the positive root tangent
subspaces to the negative root tangent subspaces. The negative subspaces are
independent of the torus and positive subspaces, giving the tangent direct sum.

## Main results

* `ReductiveGroups.ReductiveGroupData.oppositeUnipotentTangent_eq_sum`: negative root subspaces.
* `ReductiveGroups.ReductiveGroupData.oppositeUnipotent_isCompl_borel`: complementary tangents.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The tangent image of the opposite root-unipotent subgroup in the group tangent algebra. -/
abbrev oppositeUnipotentTangent : LieSubalgebra K G.tangent :=
  G.subgroupTangent G.oppositeUnipotentIdeal

/-- The opposite unipotent tangent is the sum of all negative root-character subspaces. -/
theorem oppositeUnipotentTangent_eq_sum : G.oppositeUnipotentTangent.toSubmodule =
    ⨆ (r : G.rootIndex) (_ : ¬ G.rootBase.IsPos r), G.rootWeightSpace r := by
  change (hopfTangentImage (G.unipotentIdeal.conjugate G.longestPoint)).toSubmodule = _
  rw [conjugate_tangentImage]
  change G.unipotentTangent.toSubmodule.map
    (affineGroupAdjointLieEquiv G.longestPoint).toLinearEquiv.toLinearMap = _
  rw [G.unipotentTangent_eq_iSup_pos]
  simp_rw [Submodule.map_iSup]
  change (⨆ (r : G.rootIndex) (_ : G.rootBase.IsPos r),
    (G.rootWeightSpace r).map
      (affineGroupAdjointLieEquiv (G.weylPoint G.longestElement)).toLinearEquiv.toLinearMap) = _
  simp_rw [G.weylPoint_rootWeightSpace]
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    exact le_iSup₂_of_le (G.rootSystem.weylGroupToPerm G.longestElement r)
      ((G.longestElement_isPos_iff r).not.mpr (not_not.mpr hr)) le_rfl
  · refine iSup₂_le fun r hr => ?_
    have hpos := (G.longestElement_isPos_iff r).mpr hr
    have hle : G.rootWeightSpace
        (G.rootSystem.weylGroupToPerm G.longestElement
          (G.rootSystem.weylGroupToPerm G.longestElement r)) ≤
        ⨆ (s : G.rootIndex) (_ : G.rootBase.IsPos s),
          G.rootWeightSpace (G.rootSystem.weylGroupToPerm G.longestElement s) :=
      le_iSup₂_of_le (G.rootSystem.weylGroupToPerm G.longestElement r) hpos le_rfl
    simpa only [G.longestElement_root_involutive r] using hle

/-- The opposite unipotent tangent has zero intersection with the Borel tangent. -/
theorem oppositeUnipotent_disjoint_borel :
    Disjoint G.oppositeUnipotentTangent.toSubmodule G.borelTangent.toSubmodule := by
  let S : Set G.characters := G.rootCharacter '' {r | ¬ G.rootBase.IsPos r}
  have hfinite : S.Finite := (Set.toFinite {r : G.rootIndex | ¬ G.rootBase.IsPos r}).image _
  have hindep := AffineGroupCharacterWeights.iSupIndep G.torusSplit
  have hd := hindep.disjoint_biSup_biSup' disjoint_compl_right hfinite
  apply hd.mono
  · rw [G.oppositeUnipotentTangent_eq_sum]
    exact iSup₂_le fun r hr =>
      le_iSup₂_of_le (G.rootCharacter r) (⟨r, hr, rfl⟩ : G.rootCharacter r ∈ S) le_rfl
  · rw [G.borelTangent_eq_sup, G.unipotentTangent_eq_iSup_pos]
    apply sup_le
    · rw [← G.identityWeightSpace_eq_torus]
      have h1 : (1 : G.characters) ∈ Sᶜ := by
        rintro ⟨r, _, hr⟩
        exact G.rootCharacter_ne_one r hr
      exact le_iSup₂_of_le (1 : G.characters) h1 le_rfl
    · refine iSup₂_le fun r hr => ?_
      have hchar : G.rootCharacter r ∈ Sᶜ := by
        rintro ⟨s, hs, he⟩
        exact hs ((G.rootCharacter_injective he).symm ▸ hr)
      exact le_iSup₂_of_le (G.rootCharacter r) hchar le_rfl

/-- The opposite unipotent and Borel tangent images span the entire group tangent algebra. -/
theorem oppositeUnipotent_sup_borel :
    G.oppositeUnipotentTangent.toSubmodule ⊔ G.borelTangent.toSubmodule = ⊤ := by
  apply top_unique
  rw [← G.tangent_eq_torus_sup_roots]
  apply sup_le
  · intro x hx
    exact (le_sup_right : G.borelTangent.toSubmodule ≤
      G.oppositeUnipotentTangent.toSubmodule ⊔ G.borelTangent.toSubmodule)
        (G.torusTangent_le_borel hx)
  · refine iSup_le fun r => ?_
    by_cases hr : G.rootBase.IsPos r
    · exact ((G.rootWeightSpace_le_borel r).mpr hr).trans le_sup_right
    · apply le_sup_of_le_left
      rw [G.oppositeUnipotentTangent_eq_sum]
      exact le_iSup₂_of_le r hr le_rfl

/-- The opposite unipotent tangent and Borel tangent are complementary subspaces. -/
theorem oppositeUnipotent_isCompl_borel :
    IsCompl G.oppositeUnipotentTangent.toSubmodule G.borelTangent.toSubmodule :=
  ⟨G.oppositeUnipotent_disjoint_borel,
    codisjoint_iff.mpr G.oppositeUnipotent_sup_borel⟩

end ReductiveGroupData
