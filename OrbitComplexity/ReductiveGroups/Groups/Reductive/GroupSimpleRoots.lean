import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations

/-!
# Tangents of the fixed simple-root parameters

The positive and negative maps from the chosen rank-one pairs have nonzero
tangents in the corresponding simple-root character spaces.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem rootCharacter_neg (r : G.rootIndex) :
    G.rootCharacter (-r) = (G.rootCharacter r)⁻¹ := by
  have h : G.rootSystem.rootSpanMem ℤ (-r) = -G.rootSystem.rootSpanMem ℤ r := by
    apply Subtype.ext
    simp
  have hm := congrArg (G.rootCharacterMap) h
  rw [map_neg, G.rootCharacterMap_root, G.rootCharacterMap_root] at hm
  exact hm

/-- The selected positive simple-root parameter has nonzero tangent. -/
theorem simpleRootMap_tangent_ne_zero (i : G.rootBase.support) :
    gaAffineGroupTangent (G.simpleRootMap i) ≠ 0 :=
  (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)).tangent_ne_zero

/-- The selected negative simple-root parameter has nonzero tangent. -/
theorem negativeRootMap_tangent_ne_zero (i : G.rootBase.support) :
    gaAffineGroupTangent (G.negativeSimpleRootMap i) ≠ 0 :=
  (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)).partner_tangent_ne_zero

/-- The selected positive simple-root tangent has its simple-root weight. -/
theorem simpleRootMap_tangent_mem (i : G.rootBase.support) :
    gaAffineGroupTangent (G.simpleRootMap i) ∈ G.rootWeightSpace i.val :=
  (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive (G.characterRootEquiv.symm i.val)).tangent_mem

/-- The selected negative simple-root tangent has the negative simple-root weight. -/
theorem negativeRootMap_tangent_mem (i : G.rootBase.support) :
    gaAffineGroupTangent (G.negativeSimpleRootMap i) ∈ G.rootWeightSpace (-i.val) := by
  change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter (-i.val))
  rw [rootCharacter_neg]
  exact (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)).partner_tangent_mem

end ReductiveGroups.ReductiveGroupData
