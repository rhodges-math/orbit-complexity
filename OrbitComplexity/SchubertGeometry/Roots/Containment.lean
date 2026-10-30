import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIntersection
import OrbitComplexity.SchubertGeometry.Roots.Subgroups
import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTangent

/-! # Root subgroups contained in closed positive-root supports -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem chosen_tangent_ne_zero
    (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    gaAffineGroupTangent (G.borelRootMaps i) ≠ 0 := by
  rw [← G.borelRootBasis_tangent i]
  intro h
  exact G.borelRootBasis.ne_zero i (Subtype.ext h)

private theorem chosen_root (r : G.rootIndex) (hr : G.rootBase.IsPos r) :
    let i := G.borelCharacterRootEquiv.symm ⟨r, hr⟩
    G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) = r ∧
      gaAffineGroupTangent (G.borelRootMaps i) ∈ G.rootWeightSpace r := by
  let i := G.borelCharacterRootEquiv.symm ⟨r, hr⟩
  have hi : G.characterRootEquiv
      (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) = r :=
    congrArg Subtype.val (G.borelCharacterRootEquiv.apply_symm_apply ⟨r, hr⟩)
  refine ⟨hi, ?_⟩
  have hc : G.rootCharacter r = i.val := by
    rw [← hi]
    change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val
    rw [Equiv.symm_apply_apply]
    rfl
  change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
  rw [hc]
  exact G.borelRootMaps_weight i

private theorem tangent_support (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (i : borelRootCharacterIndex G.borelIdeal G.torusSplit)
    (hi : gaAffineGroupTangent (G.borelRootMaps i) ∈
      hopfTangentImage (G.rootSubsetIdeal R hR)) : i ∈ G.rootCharacters R := by
  classical
  have hmap : (Submodule.span K (G.borelRootBasis '' G.rootCharacters R)).map
      G.unipotentTangent.toSubmodule.subtype =
      Submodule.span K ((fun j => gaAffineGroupTangent (G.borelRootMaps j)) ''
        G.rootCharacters R) := by
    rw [Submodule.map_span]
    simp only [Set.image_image, Submodule.subtype_apply, G.borelRootBasis_tangent]
  have hs : gaAffineGroupTangent (G.borelRootMaps i) ∈ Submodule.span K
      ((fun j => gaAffineGroupTangent (G.borelRootMaps j)) '' G.rootCharacters R) := by
    rw [← G.rootSubsetTangent_eq_span]
    exact hi
  rw [← hmap] at hs
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hs
  have heq : v = G.borelRootBasis i :=
    Subtype.ext (he.trans (G.borelRootBasis_tangent i).symm)
  rw [heq] at hv
  exact G.borelRootBasis.self_mem_span_image.mp hv

/-- A canonical root group lies in a positive-root support exactly at its supported roots. -/
theorem rootSubgroup_le_support (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (r : G.rootIndex) :
    rootSubgroupPoints G r ≤ G.rootSubsetPoints R hR ↔ G.rootBase.IsPos r ∧ r ∈ R := by
  constructor
  · intro h
    have hd : gaAffineGroupTangent (rootParameterMap G r) ∈
        hopfTangentImage (G.rootSubsetIdeal R hR) :=
      gaTangent_mem_of_point_one_mem (rootParameterMap G r) (G.rootSubsetIdeal R hR)
        (h ⟨Multiplicative.ofAdd 1, rfl⟩)
    have hdB : gaAffineGroupTangent (rootParameterMap G r) ∈ G.borelTangent :=
      G.unipotentTangent_le_borel
        (hopfQuotient_tangentImage_antitone _ G.unipotentIdeal
          (G.unipotentIdeal_le_rootSubset R hR) hd)
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
      (G.rootWeightSpace_finrank r) (rootParameterMap_tangent_mem G r)
      (rootParameterMap_tangent_ne_zero G r)
    have hr : G.rootBase.IsPos r := (G.rootWeightSpace_le_borel r).mp (by
      rw [hspan]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hdB))
    let i := G.borelCharacterRootEquiv.symm ⟨r, hr⟩
    have hc := chosen_root G r hr
    have hpoint : gaParameterPoint (G.borelRootMaps i) (1 : K) ∈ rootSubgroupPoints G r := by
      change _ ∈ (rootSubgroupPoints G r : Set G.points)
      rw [← rootSubgroupPoints_eq_range G r (G.borelRootMaps i) hc.2
        (chosen_tangent_ne_zero G i)]
      exact ⟨1, rfl⟩
    have hi := tangent_support G R hR i
      (gaTangent_mem_of_point_one_mem (G.borelRootMaps i) (G.rootSubsetIdeal R hR) (h hpoint))
    exact ⟨hr, hc.1 ▸ hi⟩
  · rintro ⟨hr, hrR⟩ g hg
    obtain ⟨a, rfl⟩ := hg
    exact GaParameterPoint.mem_of_tangent_mem_quotient (rootParameterMap G r)
      (G.rootSubsetIdeal R hR)
      (G.rootWeightSpace_le_rootSubset R hR r hr hrR (rootParameterMap_tangent_mem G r))
      a.toAdd

/-- The canonical root groups in a Schubert unipotent subgroup are precisely its inversions. -/
theorem rootSubgroup_le_schubert (w : G.weylGroup) (r : G.rootIndex) :
    rootSubgroupPoints G r ≤ schubertUnipotentPoints G w ↔
      r ∈ leftRootInversionIndices G.rootBase w := by
  rw [rootSubgroup_le_support]
  exact and_iff_right_of_imp (fun hr => hr.1)

/-- The root groups in the chosen unipotent radical are exactly the positive root groups. -/
theorem rootSubgroup_le_unipotent (r : G.rootIndex) :
    rootSubgroupPoints G r ≤ G.unipotentPoints ↔ G.rootBase.IsPos r := by
  simpa only [G.fullRootPoints_eq_unipotent, Set.mem_ofPred_eq, and_self] using
    rootSubgroup_le_support G {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) r

/-- The root groups in the opposite unipotent radical are exactly the negative root groups. -/
theorem rootSubgroup_le_opposite (r : G.rootIndex) :
    rootSubgroupPoints G r ≤ G.oppositeUnipotentPoints ↔ ¬ G.rootBase.IsPos r := by
  constructor
  · intro h hr
    have hd : gaAffineGroupTangent (rootParameterMap G r) ∈ G.oppositeUnipotentTangent :=
      gaTangent_mem_of_point_one_mem (rootParameterMap G r) G.oppositeUnipotentIdeal
        (h ⟨Multiplicative.ofAdd 1, rfl⟩)
    have hdB : gaAffineGroupTangent (rootParameterMap G r) ∈ G.borelTangent :=
      (G.rootWeightSpace_le_borel r).mpr hr (rootParameterMap_tangent_mem G r)
    have hz : gaAffineGroupTangent (rootParameterMap G r) ∈
        (⊥ : Submodule K G.tangent) :=
      (disjoint_iff.mp G.oppositeUnipotent_disjoint_borel) ▸ ⟨hd, hdB⟩
    exact rootParameterMap_tangent_ne_zero G r hz
  · intro hr g hg
    obtain ⟨a, rfl⟩ := hg
    apply GaParameterPoint.mem_of_tangent_mem_quotient (rootParameterMap G r)
      G.oppositeUnipotentIdeal
    change _ ∈ G.oppositeUnipotentTangent.toSubmodule
    rw [G.oppositeUnipotentTangent_eq_sum]
    have hle : G.rootWeightSpace r ≤
        ⨆ (s : G.rootIndex) (_ : ¬ G.rootBase.IsPos s), G.rootWeightSpace s :=
      le_iSup₂_of_le r hr le_rfl
    exact hle (rootParameterMap_tangent_mem G r)

end
end SchubertGeometry
