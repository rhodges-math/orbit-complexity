import OrbitComplexity.ReductiveGroups.Roots.Coxeter.SimpleOrderThreeStrings
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCorootSquare

/-! # Tangent strings of adjacent simple roots -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti LieAlgebra
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] (G : ReductiveGroupData K)

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

private theorem root_character_of_sum (r s t : G.rootIndex)
    (ht : G.rootSystem.root t = G.rootSystem.root r + G.rootSystem.root s) :
    G.rootCharacter t = G.rootCharacter r * G.rootCharacter s := by
  have he : G.rootSystem.rootSpanMem ℤ t =
      G.rootSystem.rootSpanMem ℤ r + G.rootSystem.rootSpanMem ℤ s := Subtype.ext ht
  have hm : (G.rootCharacter t).toAdd =
      (G.rootCharacter r).toAdd + (G.rootCharacter s).toAdd :=
    (G.rootCharacterMap_root t).symm.trans
      ((congrArg G.rootCharacterMap he).trans
        ((map_add G.rootCharacterMap _ _).trans
          (congrArg₂ (fun a b => a + b)
            (G.rootCharacterMap_root r) (G.rootCharacterMap_root s))))
  exact congrArg Multiplicative.ofAdd hm

private theorem root_double_bracket_zero (r s t : G.rootIndex)
    (ht : G.rootSystem.root t = G.rootSystem.root r + G.rootSystem.root s)
    (hne : G.rootSystem.root s + 2 • G.rootSystem.root r ≠ 0)
    (hnot : G.rootSystem.root s + 2 • G.rootSystem.root r ∉ Set.range G.rootSystem.root)
    (d e : G.tangent) (hd : d ∈ G.rootWeightSpace r) (he : e ∈ G.rootWeightSpace s) :
    ⁅d, ⁅d, e⁆⁆ = 0 := by
  have hb := lie_mem_affineGroupCharacterWeightSpace G.torusSplit
    (G.rootCharacter r) (G.rootCharacter s) d e hd he
  rw [← root_character_of_sum G r s t ht] at hb
  have heq : G.rootSystem.root r + G.rootSystem.root t =
      G.rootSystem.root s + 2 • G.rootSystem.root r := by
    rw [ht, two_smul]
    abel
  apply root_bracket_zero G r t _ _ d ⁅d, e⁆ hd hb
  · rw [heq]
    exact hne
  · rw [heq]
    exact hnot

private theorem simple_cartan_root_pairing (i : G.rootBase.support) (r : G.rootIndex) :
    characterDifferentialOnImage G.torusSplit G.split_surjective
      (G.rootCharacter r) (Coroot.simpleCartan G i) = G.rootSystem.pairing r i.val := by
  obtain ⟨l, _, _, hcast, _, _, hroot, _, _⟩ := Coroot.simple_coroot_exists G i
  calc
    _ = (l (G.rootCharacter r).toAdd : K) := (hcast _).symm
    _ = (G.rootSystem.pairingIn ℤ r i.val : K) := congrArg (fun z : ℤ => (z : K)) (hroot r)
    _ = _ := G.rootSystem.algebraMap_pairingIn ℤ r i.val

private theorem simple_cartan_root_lie (i : G.rootBase.support) (r : G.rootIndex)
    (d : G.tangent) (hd : d ∈ G.rootWeightSpace r) :
    ⁅(Coroot.simpleCartan G i : G.tangent), d⁆ = G.rootSystem.pairing r i.val • d := by
  let e := diagonalizableTangentEquivImage G.torusSplit G.split_surjective
  let h := e.symm (Coroot.simpleCartan G i)
  have hh : e h = Coroot.simpleCartan G i := e.apply_symm_apply _
  have hhval : derivationComp (B := K) G.torusSplit h =
      (Coroot.simpleCartan G i : G.tangent) := congrArg Subtype.val hh
  have hb := bracket_eq_character_derivative G.torusSplit (G.rootCharacter r) h d hd
  change ⁅derivationComp (B := K) G.torusSplit h, d⁆ =
    characterDifferential (G.rootCharacter r) h • d at hb
  have hc := characterDifferentialOnImage_apply_equiv G.torusSplit
    G.split_surjective (G.rootCharacter r) h
  rw [hh] at hc
  rw [← hhval]
  exact hb.trans (congrArg (fun a : K => a • d)
    (hc.symm.trans (simple_cartan_root_pairing G i r)))

/-- Adjacent simple parameters satisfy both first-order tangent strings in the original group. -/
theorem simple_root_a2_tangent_strings (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 3) :
    let e := gaAffineGroupTangent (G.simpleRootMap i)
    let f := gaAffineGroupTangent (G.negativeSimpleRootMap i)
    let v := gaAffineGroupTangent (G.simpleRootMap j)
    let w := gaAffineGroupTangent (G.negativeSimpleRootMap j)
    (⁅f, v⁆ = 0 ∧ ⁅e, ⁅e, v⁆⁆ = 0 ∧ ⁅f, ⁅e, v⁆⁆ = v) ∧
    (⁅e, w⁆ = 0 ∧ ⁅f, ⁅f, w⁆⁆ = 0 ∧ ⁅e, ⁅f, w⁆⁆ = w) := by
  let e := gaAffineGroupTangent (G.simpleRootMap i)
  let f := gaAffineGroupTangent (G.negativeSimpleRootMap i)
  let v := gaAffineGroupTangent (G.simpleRootMap j)
  let w := gaAffineGroupTangent (G.negativeSimpleRootMap j)
  change (⁅f, v⁆ = 0 ∧ ⁅e, ⁅e, v⁆⁆ = 0 ∧ ⁅f, ⁅e, v⁆⁆ = v) ∧
    (⁅e, w⁆ = 0 ∧ ⁅f, ⁅f, w⁆⁆ = 0 ∧ ⁅e, ⁅f, w⁆⁆ = w)
  obtain ⟨⟨_, hq⟩, hsum, ⟨hdiff, hdiffnot⟩, ⟨h2, h2not⟩, _⟩ :=
    order_three_simple_root_strings G.rootSystem G.rootBase i j h
  obtain ⟨t, ht⟩ := hsum
  have hneg (r : G.rootIndex) : G.rootSystem.root (-r) = -G.rootSystem.root r := rfl
  have hnd : G.rootSystem.root (-i.val) + G.rootSystem.root j.val =
      -(G.rootSystem.root i.val - G.rootSystem.root j.val) := by
    rw [hneg]
    abel
  have hfv : ⁅f, v⁆ = 0 := by
    apply root_bracket_zero G (-i.val) j.val _ _ f v
      (G.negativeRootMap_tangent_mem i) (G.simpleRootMap_tangent_mem j)
    · rw [hnd]
      exact neg_ne_zero.mpr hdiff
    · rw [hnd, G.rootSystem.neg_mem_range_root_iff]
      exact hdiffnot
  have hew : ⁅e, w⁆ = 0 := by
    apply root_bracket_zero G i.val (-j.val) _ _ e w
      (G.simpleRootMap_tangent_mem i) (G.negativeRootMap_tangent_mem j)
    · rw [hneg, ← sub_eq_add_neg]
      exact hdiff
    · rw [hneg, ← sub_eq_add_neg]
      exact hdiffnot
  have heev : ⁅e, ⁅e, v⁆⁆ = 0 :=
    root_double_bracket_zero G i.val j.val t ht h2 h2not e v
      (G.simpleRootMap_tangent_mem i) (G.simpleRootMap_tangent_mem j)
  have htn : G.rootSystem.root (-t) =
      G.rootSystem.root (-i.val) + G.rootSystem.root (-j.val) := by
    rw [hneg, hneg, hneg, ht]
    abel
  have hn2 : G.rootSystem.root (-j.val) + 2 • G.rootSystem.root (-i.val) =
      -(G.rootSystem.root j.val + 2 • G.rootSystem.root i.val) := by
    rw [hneg, hneg, two_smul, two_smul]
    abel
  have hffw : ⁅f, ⁅f, w⁆⁆ = 0 := by
    apply root_double_bracket_zero G (-i.val) (-j.val) (-t) htn _ _ f w
      (G.negativeRootMap_tangent_mem i) (G.negativeRootMap_tangent_mem j)
    · rw [hn2]
      exact neg_ne_zero.mpr h2
    · rw [hn2, G.rootSystem.neg_mem_range_root_iff]
      exact h2not
  have hfield : G.rootSystem.pairing j.val i.val = (-1 : K) := by
    rw [← G.rootSystem.algebraMap_pairingIn ℤ j.val i.val, hq]
    simp
  have hhE : ⁅⁅e, f⁆, v⁆ = -v := by
    have he := simple_cartan_root_lie G i j.val v (G.simpleRootMap_tangent_mem j)
    change ⁅⁅e, f⁆, v⁆ = G.rootSystem.pairing j.val i.val • v at he
    exact he.trans ((congrArg (fun a : K => a • v) hfield).trans (neg_one_smul K v))
  have hnfield : G.rootSystem.pairing (-j.val) i.val = (1 : K) := by
    calc
      _ = G.rootSystem.toLinearMap (G.rootSystem.root (-j.val))
          (G.rootSystem.coroot i.val) := by rw [G.rootSystem.root_coroot_eq_pairing]
      _ = -(G.rootSystem.toLinearMap (G.rootSystem.root j.val)
          (G.rootSystem.coroot i.val)) := by rw [hneg, map_neg, LinearMap.neg_apply]
      _ = 1 := by rw [G.rootSystem.root_coroot_eq_pairing, hfield, neg_neg]
  have hhF : ⁅⁅e, f⁆, w⁆ = w := by
    have he := simple_cartan_root_lie G i (-j.val) w
      (G.negativeRootMap_tangent_mem j)
    change ⁅⁅e, f⁆, w⁆ = G.rootSystem.pairing (-j.val) i.val • w at he
    exact he.trans ((congrArg (fun a : K => a • w) hnfield).trans (one_smul K w))
  have hfev : ⁅f, ⁅e, v⁆⁆ = v := by
    have hjac := lie_lie e f v
    rw [hhE, hfv, lie_zero, zero_sub] at hjac
    exact neg_injective hjac.symm
  have hefw : ⁅e, ⁅f, w⁆⁆ = w := by
    have hjac := lie_lie e f w
    rw [hhF, hew, lie_zero, sub_zero] at hjac
    exact hjac.symm
  exact ⟨⟨hfv, heev, hfev⟩, ⟨hew, hffw, hefw⟩⟩

end ReductiveGroups.ReductiveGroupData
