import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupCommutation
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import TauCeti.LinearAlgebra.RootSystem.BraidRelation

/-! # Commutation of rank-one subgroup products -/

noncomputable section
namespace ReductiveGroups
open TauCeti
universe u
variable {K B : Type u} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

private theorem triple_commute
    (x y z w : B →ₐc[K] SymmetricAlgebra K K)
    (hxz : ⁅gaAffineGroupTangent x, gaAffineGroupTangent z⁆ = 0)
    (hxw : ⁅gaAffineGroupTangent x, gaAffineGroupTangent w⁆ = 0)
    (hyz : ⁅gaAffineGroupTangent y, gaAffineGroupTangent z⁆ = 0)
    (hyw : ⁅gaAffineGroupTangent y, gaAffineGroupTangent w⁆ = 0) :
    Commute
      (gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
          gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)))
      (gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints w (Multiplicative.ofAdd (-1 : K)) *
          gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K))) := by
  have h11 := GaAffineGroupPoints.commute_of_tangent_bracket_zero x z hxz 1 1
  have h12 := GaAffineGroupPoints.commute_of_tangent_bracket_zero x w hxw 1 (-1)
  have h21 := GaAffineGroupPoints.commute_of_tangent_bracket_zero y z hyz (-1) 1
  have h22 := GaAffineGroupPoints.commute_of_tangent_bracket_zero y w hyw (-1) (-1)
  have h1 := (h11.mul_right h12).mul_right h11
  have h2 := (h21.mul_right h22).mul_right h21
  exact (h1.mul_left h2).mul_left h1


namespace ReductiveGroupData
variable [IsAlgClosed K] (G : ReductiveGroupData K)

private theorem root_eq_sum_of_character (r s t : G.rootIndex)
    (h : G.rootCharacter t = G.rootCharacter r * G.rootCharacter s) :
    G.rootSystem.root t = G.rootSystem.root r + G.rootSystem.root s := by
  have hm : G.rootCharacterMap
      (G.rootSystem.rootSpanMem ℤ r + G.rootSystem.rootSpanMem ℤ s) =
        (G.rootCharacter r).toAdd + (G.rootCharacter s).toAdd :=
    (map_add G.rootCharacterMap _ _).trans
      (congrArg₂ (fun a b => a + b)
        (G.rootCharacterMap_root r) (G.rootCharacterMap_root s))
  have ht : G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ t) =
      G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ r +
        G.rootSystem.rootSpanMem ℤ s) :=
    (G.rootCharacterMap_root t).trans ((congrArg Multiplicative.toAdd h).trans hm.symm)
  exact congrArg Subtype.val (G.rootCharacterMap_injective ht)

private theorem root_bracket_zero (r s : G.rootIndex)
    (hne : G.rootSystem.root r + G.rootSystem.root s ≠ 0)
    (hnot : G.rootSystem.root r + G.rootSystem.root s ∉ Set.range G.rootSystem.root)
    (d e : G.tangent) (hd : d ∈ G.rootWeightSpace r) (he : e ∈ G.rootWeightSpace s) :
    ⁅d, e⁆ = 0 := by
  have hchar : G.rootCharacter r * G.rootCharacter s ≠ 1 := by
    intro h
    have hm : G.rootCharacterMap
        (G.rootSystem.rootSpanMem ℤ r + G.rootSystem.rootSpanMem ℤ s) =
          G.rootCharacterMap 0 := by
      rw [map_add, G.rootCharacterMap_root r, G.rootCharacterMap_root s, map_zero]
      exact congrArg Multiplicative.toAdd h
    exact hne (congrArg Subtype.val (G.rootCharacterMap_injective hm))
  by_contra hz
  have hb := lie_mem_affineGroupCharacterWeightSpace G.torusSplit
    (G.rootCharacter r) (G.rootCharacter s) d e hd he
  have hspace : affineGroupCharacterWeightSpace G.torusSplit
      (G.rootCharacter r * G.rootCharacter s) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨⁅d, e⁆, hb, hz⟩
  let chi : {a : G.characters //
      affineGroupCharacterWeightSpace G.torusSplit a ≠ ⊥ ∧ a ≠ 1} :=
    ⟨G.rootCharacter r * G.rootCharacter s, hspace, hchar⟩
  let t := G.characterRootEquiv chi
  have ht : G.rootCharacter t = G.rootCharacter r * G.rootCharacter s :=
    congrArg Subtype.val (G.characterRootEquiv.symm_apply_apply chi)
  exact hnot ⟨t, root_eq_sum_of_character G r s t ht⟩

private theorem reflection_commute_of_four (i j : G.rootBase.support)
    (hee : ⁅gaAffineGroupTangent (G.simpleRootMap i),
      gaAffineGroupTangent (G.simpleRootMap j)⁆ = 0)
    (hef : ⁅gaAffineGroupTangent (G.simpleRootMap i),
      gaAffineGroupTangent (G.negativeSimpleRootMap j)⁆ = 0)
    (hfe : ⁅gaAffineGroupTangent (G.negativeSimpleRootMap i),
      gaAffineGroupTangent (G.simpleRootMap j)⁆ = 0)
    (hff : ⁅gaAffineGroupTangent (G.negativeSimpleRootMap i),
      gaAffineGroupTangent (G.negativeSimpleRootMap j)⁆ = 0) :
    Commute (G.reflectionPoint i.val) (G.reflectionPoint j.val) :=
  triple_commute (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    (G.simpleRootMap j) (G.negativeSimpleRootMap j) hee hef hfe hff

private theorem orthogonal_simple_sums (i j : G.rootBase.support)
    (h : G.rootSystem.IsOrthogonal i.val j.val) :
    (G.rootSystem.root i.val + G.rootSystem.root j.val ≠ 0 ∧
      G.rootSystem.root i.val + G.rootSystem.root j.val ∉ Set.range G.rootSystem.root) ∧
    (G.rootSystem.root i.val - G.rootSystem.root j.val ≠ 0 ∧
      G.rootSystem.root i.val - G.rootSystem.root j.val ∉ Set.range G.rootSystem.root) := by
  have hij : i ≠ j := by
    intro heq
    subst j
    have hz := h.1
    simp only [RootPairing.pairing_same] at hz
    exact two_ne_zero hz
  have hval : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
  have hsum : G.rootSystem.root i.val + G.rootSystem.root j.val ≠ 0 := by
    intro hz
    exact G.rootBase.root_ne_neg_of_ne i.property j.property hval
      (eq_neg_of_add_eq_zero_left hz)
  have hdiff : G.rootSystem.root i.val - G.rootSystem.root j.val ≠ 0 := by
    intro hz
    exact hval (G.rootSystem.root.injective (sub_eq_zero.mp hz))
  have hp : G.rootSystem.pairingIn ℤ i.val j.val = 0 := by
    apply FaithfulSMul.algebraMap_injective ℤ K
    simpa only [G.rootSystem.algebraMap_pairingIn, map_zero] using h.1
  have htop : G.rootSystem.chainTopCoeff j.val i.val = 0 := by
    have ht := G.rootBase.chainTopCoeff_eq_of_ne hij.symm
    rw [hp, neg_zero] at ht
    exact_mod_cast ht
  have hnot := (G.rootSystem.chainTopCoeff_eq_zero_iff.mp htop).resolve_left
    (not_not_intro (G.rootBase.linearIndependent_pair_of_ne hij.symm))
  exact ⟨⟨hsum, hnot⟩, ⟨hdiff, G.rootBase.sub_notMem_range_root i.property j.property⟩⟩

/-- Fixed representatives of orthogonal simple roots commute in the full group. -/
theorem reflectionPoints_commute (i j : G.rootBase.support)
    (h : G.rootSystem.IsOrthogonal i.val j.val) :
    Commute (G.reflectionPoint i.val) (G.reflectionPoint j.val) := by
  obtain ⟨⟨hsum, hsumroot⟩, ⟨hdiff, hdiffroot⟩⟩ := orthogonal_simple_sums G i j h
  have hneg (r : G.rootIndex) : G.rootSystem.root (-r) = -G.rootSystem.root r := rfl
  have hnd : G.rootSystem.root (-i.val) + G.rootSystem.root j.val =
      -(G.rootSystem.root i.val - G.rootSystem.root j.val) := by
    rw [hneg]
    abel
  have hns : G.rootSystem.root (-i.val) + G.rootSystem.root (-j.val) =
      -(G.rootSystem.root i.val + G.rootSystem.root j.val) := by
    rw [hneg, hneg]
    abel
  apply reflection_commute_of_four G i j
  · exact root_bracket_zero G i.val j.val hsum hsumroot _ _
      (G.simpleRootMap_tangent_mem i) (G.simpleRootMap_tangent_mem j)
  · apply root_bracket_zero G i.val (-j.val) _ _ _ _
      (G.simpleRootMap_tangent_mem i) (G.negativeRootMap_tangent_mem j)
    · rw [hneg, ← sub_eq_add_neg]
      exact hdiff
    · rw [hneg, ← sub_eq_add_neg]
      exact hdiffroot
  · apply root_bracket_zero G (-i.val) j.val _ _ _ _
      (G.negativeRootMap_tangent_mem i) (G.simpleRootMap_tangent_mem j)
    · rw [hnd]
      exact neg_ne_zero.mpr hdiff
    · rw [hnd, G.rootSystem.neg_mem_range_root_iff]
      exact hdiffroot
  · apply root_bracket_zero G (-i.val) (-j.val) _ _ _ _
      (G.negativeRootMap_tangent_mem i) (G.negativeRootMap_tangent_mem j)
    · rw [hns]
      exact neg_ne_zero.mpr hsum
    · rw [hns, G.rootSystem.neg_mem_range_root_iff]
      exact hsumroot

/-- Order two for the simple-reflection product gives the exact commuting braid in the group. -/
theorem reflectionPoints_commute_of_order_two (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 2) :
    Commute (G.reflectionPoint i.val) (G.reflectionPoint j.val) := by
  apply reflectionPoints_commute G i j
  exact (TauCeti.coxeterMatrixOfBase_eq_two_iff G.rootSystem G.rootBase i j).mp
    ((RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
      G.rootSystem G.rootBase i j).symm.trans h)

end ReductiveGroupData

end ReductiveGroups
