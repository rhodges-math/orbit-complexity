import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPointSubgroup

/-!
# Root tangent spaces inside closed root-support groups

A supported chosen root map takes every parameter into its closed subgroup.
Its tangent is nonzero in the corresponding one-dimensional root space,
so that whole root space lies in the subgroup tangent image.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Each chosen root map in a closed support takes every parameter into that subgroup. -/
theorem rootMapPoint_mem_rootSubset (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (i : G.rootCharacters R) (a : K) :
    gaParameterPoint (G.borelRootMaps i.val) a ∈ G.rootSubsetPoints R hR := by
  have hxU (j) : gaAffineGroupTangent (G.borelRootMaps j) ∈ G.unipotentTangent :=
    G.borelRootBasis_tangent j ▸ (G.borelRootBasis j).property
  let v := borelRootSubsetProduct G.borelIdeal G.torusSplit G.split_surjective
    G.borelRootMaps hxU (G.rootCharacters R) [i] (fun _ => a)
  have hv : v ∈ borelRootSubsetSubgroup G.torusIdeal G.borelIdeal G.borel_le_torus
      G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
      G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
      (G.rootCharacters R) (G.rootCharacters_closed R hR) :=
    borelRootSubsetProduct_mem G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
      G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
      G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight hxU
      (G.rootCharacters_closed R hR) [i] (fun _ => a)
  apply (congrArg (fun H : Subgroup G.points =>
    gaParameterPoint (G.borelRootMaps i.val) a ∈ H) (G.rootSubsetPoints_eq R hR)).mpr
  refine Subgroup.mem_map.mpr ⟨v, hv, ?_⟩
  change v.val = gaParameterPoint (G.borelRootMaps i.val) a
  simp only [v, borelRootSubsetProduct, List.map_singleton, List.prod_singleton]

/-- The tangent of each chosen root map belongs to its closed root-support subgroup. -/
theorem rootMapTangent_mem_rootSubset (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (i : G.rootCharacters R) :
    gaAffineGroupTangent (G.borelRootMaps i.val) ∈ hopfTangentImage (G.rootSubsetIdeal R hR) :=
  gaTangent_mem_of_point_one_mem (G.borelRootMaps i.val) (G.rootSubsetIdeal R hR)
    (G.rootMapPoint_mem_rootSubset R hR i 1)

/-- A positive root space in a closed support lies in the subgroup tangent. -/
theorem rootWeightSpace_le_rootSubset (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (r : G.rootIndex)
    (hr : G.rootBase.IsPos r) (hrR : r ∈ R) :
    G.rootWeightSpace r ≤ (hopfTangentImage (G.rootSubsetIdeal R hR)).toSubmodule := by
  let i := G.borelCharacterRootEquiv.symm ⟨r, hr⟩
  have hi : G.characterRootEquiv
      (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) = r :=
    congrArg Subtype.val (G.borelCharacterRootEquiv.apply_symm_apply ⟨r, hr⟩)
  have hchar : G.rootCharacter r = i.val := by
    rw [← hi]
    change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val
    rw [Equiv.symm_apply_apply]
    rfl
  have hweight : gaAffineGroupTangent (G.borelRootMaps i) ∈ G.rootWeightSpace r := by
    change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
    rw [hchar]
    exact G.borelRootMaps_weight i
  have hne : gaAffineGroupTangent (G.borelRootMaps i) ≠ 0 := by
    rw [← G.borelRootBasis_tangent i]
    intro h
    exact G.borelRootBasis.ne_zero i (Subtype.ext h)
  have hiR : i ∈ G.rootCharacters R := by
    change G.characterRootEquiv
      (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) ∈ R
    rwa [hi]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (G.rootWeightSpace_finrank r) hweight hne
  rw [hspan]
  apply Submodule.span_le.mpr
  exact Set.singleton_subset_iff.mpr (G.rootMapTangent_mem_rootSubset R hR ⟨i, hiR⟩)

/-- Inclusion of closed root supports gives inclusion of their rational-point subgroups. -/
theorem rootSubsetPoints_mono (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (hRS : R ⊆ S) : G.rootSubsetPoints R hR ≤ G.rootSubsetPoints S hS := by
  intro g hg
  have hmap := (congrArg (fun H : Subgroup G.points => g ∈ H)
    (G.rootSubsetPoints_eq R hR)).mp hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hmap
  apply (congrArg (fun H : Subgroup G.points => u.val ∈ H)
    (G.rootSubsetPoints_eq S hS)).mpr
  refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
  change ∀ i, i ∉ G.rootCharacters S → _
  intro i hi
  exact hu i (fun hiR => hi (hRS hiR))

end ReductiveGroups.ReductiveGroupData
