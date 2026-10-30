import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBraidFourRoots
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupCommutation
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupReflectionSquare

/-! # Commutation with a reflected long-root subgroup -/

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

private theorem conjugate_tangent_mem (j : G.rootBase.support)
    (r : G.rootIndex) (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r) :
    gaAffineGroupTangent
      (x.comp (affineGroupConjugationBialgHom (G.reflectionPoint j.val))) ∈
      G.rootWeightSpace (G.rootSystem.reflectionPerm j.val r) := by
  rw [gaTangent_comp_conjugation]
  rw [← G.isBruhatSystem.weyl.transport_reflection j.val r]
  exact Submodule.mem_map.mpr ⟨_, hx, rfl⟩

/-- A long simple representative commutes with its conjugate by the adjacent short one. -/
theorem reflection_conjugate_commute (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -2) :
    Commute (G.reflectionPoint i.val)
      (G.reflectionPoint j.val * G.reflectionPoint i.val *
        (G.reflectionPoint j.val)⁻¹) := by
  let r := G.rootSystem.reflectionPerm j.val i.val
  let s := G.rootSystem.reflectionPerm j.val (-i.val)
  let z := (G.simpleRootMap i).comp
    (affineGroupConjugationBialgHom (G.reflectionPoint j.val))
  let w := (G.negativeSimpleRootMap i).comp
    (affineGroupConjugationBialgHom (G.reflectionPoint j.val))
  have hz : gaAffineGroupTangent z ∈ G.rootWeightSpace r :=
    conjugate_tangent_mem G j i.val _ (G.simpleRootMap_tangent_mem i)
  have hw : gaAffineGroupTangent w ∈ G.rootWeightSpace s :=
    conjugate_tangent_mem G j (-i.val) _ (G.negativeRootMap_tangent_mem i)
  have hneg (a : G.rootIndex) : G.rootSystem.root (-a) = -G.rootSystem.root a := rfl
  have hs : G.rootSystem.root s = -G.rootSystem.root r := by
    dsimp only [r, s]
    rw [G.rootSystem.root_reflectionPerm, G.rootSystem.root_reflectionPerm, hneg,
      map_neg]
  obtain ⟨⟨hplus, hplusroot⟩, ⟨hminus, hminusroot⟩⟩ := G.orderFour_root_sums i j hp
  have h11 := root_bracket_zero G i.val r hplus hplusroot _ _
    (G.simpleRootMap_tangent_mem i) hz
  have h12 : ⁅gaAffineGroupTangent (G.simpleRootMap i), gaAffineGroupTangent w⁆ = 0 := by
    apply root_bracket_zero G i.val s _ _ _ _ (G.simpleRootMap_tangent_mem i) hw
    · rw [hs, ← sub_eq_add_neg]
      exact hminus
    · rw [hs, ← sub_eq_add_neg]
      exact hminusroot
  have h21 : ⁅gaAffineGroupTangent (G.negativeSimpleRootMap i),
      gaAffineGroupTangent z⁆ = 0 := by
    apply root_bracket_zero G (-i.val) r _ _ _ _ (G.negativeRootMap_tangent_mem i) hz
    · have he : G.rootSystem.root (-i.val) + G.rootSystem.root r =
          -(G.rootSystem.root i.val - G.rootSystem.root r) := by rw [hneg]; abel
      rw [he]
      exact neg_ne_zero.mpr hminus
    · have he : G.rootSystem.root (-i.val) + G.rootSystem.root r =
          -(G.rootSystem.root i.val - G.rootSystem.root r) := by rw [hneg]; abel
      rw [he, G.rootSystem.neg_mem_range_root_iff]
      exact hminusroot
  have h22 : ⁅gaAffineGroupTangent (G.negativeSimpleRootMap i),
      gaAffineGroupTangent w⁆ = 0 := by
    apply root_bracket_zero G (-i.val) s _ _ _ _ (G.negativeRootMap_tangent_mem i) hw
    · have he : G.rootSystem.root (-i.val) + G.rootSystem.root s =
          -(G.rootSystem.root i.val + G.rootSystem.root r) := by rw [hneg, hs]; abel
      rw [he]
      exact neg_ne_zero.mpr hplus
    · have he : G.rootSystem.root (-i.val) + G.rootSystem.root s =
          -(G.rootSystem.root i.val + G.rootSystem.root r) := by rw [hneg, hs]; abel
      rw [he, G.rootSystem.neg_mem_range_root_iff]
      exact hplusroot
  have hc := triple_commute (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    z w h11 h12 h21 h22
  dsimp only [z, w] at hc
  simp only [gaPoints_comp_conjugation] at hc
  have hi : G.reflectionPoint i.val =
      gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (-1 : K)) *
          gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) := rfl
  rw [hi]
  convert hc using 1
  group

end ReductiveGroupData
end ReductiveGroups
