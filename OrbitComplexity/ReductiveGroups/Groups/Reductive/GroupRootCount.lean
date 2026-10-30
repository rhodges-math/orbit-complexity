import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.LongestCount

/-!
# Counting Borel root characters

The characters indexing Borel root coordinates correspond exactly to the positive
roots selected by the Borel subgroup. Their number is therefore the inversion
count of the longest Weyl element.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def borelCharacterToRoot (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    {r : G.rootIndex // G.rootBase.IsPos r} :=
  ⟨G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i),
    borelRootBase_isPos G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
      G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive i⟩

/-- The characters indexing Borel root coordinates correspond exactly to positive roots. -/
def borelCharacterRootEquiv :
    borelRootCharacterIndex G.borelIdeal G.torusSplit ≃
      {r : G.rootIndex // G.rootBase.IsPos r} :=
  Equiv.ofBijective G.borelCharacterToRoot ⟨by
    intro i j h
    apply Subtype.ext
    have hroot := congrArg Subtype.val h
    have hchar := G.characterRootEquiv.injective hroot
    exact congrArg
      (fun a : {χ : G.characters //
          affineGroupCharacterWeightSpace G.torusSplit χ ≠ ⊥ ∧ χ ≠ 1} => a.val) hchar, by
    intro r
    have hle : G.rootWeightSpace r.val ≤ G.borelTangent.toSubmodule :=
      (G.rootWeightSpace_le_borel r.val).mpr r.property
    have hne : G.borelTangent.toSubmodule ⊓
        affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r.val) ≠ ⊥ := by
      change G.borelTangent.toSubmodule ⊓ G.rootWeightSpace r.val ≠ ⊥
      rw [inf_eq_right.mpr hle]
      exact G.rootWeightSpace_ne_bot r.val
    let i : borelRootCharacterIndex G.borelIdeal G.torusSplit :=
      ⟨G.rootCharacter r.val, G.rootCharacter_ne_one r.val, hne⟩
    refine ⟨i, Subtype.ext ?_⟩
    change G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) = r.val
    have he : borelRootCharacterOccurring G.borelIdeal G.torusSplit i =
        G.characterRootEquiv.symm r.val := by
      apply Subtype.ext
      rfl
    rw [he, Equiv.apply_symm_apply]⟩

/-- The number of Borel root-coordinate characters is the longest Weyl inversion count. -/
theorem natCard_borelCharacters :
    Nat.card (borelRootCharacterIndex G.borelIdeal G.torusSplit) =
      rootInversionCount G.rootBase G.longestElement := by
  rw [Nat.card_congr G.borelCharacterRootEquiv]
  exact (rootInversionCount_longest G.rootBase).symm

end ReductiveGroupData
