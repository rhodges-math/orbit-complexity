import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSupport
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootLogarithmDifferential

/-!
# Tangent spaces of closed root-support groups

Logarithm-coordinate equations cut out the prescribed span of root tangents.
For a singleton positive support the subgroup tangent is its root weight space.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem logarithm_mem_rootIdeal (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) (hi : i ∉ G.rootCharacters R) :
    borelRootLogarithmCoordinate G.borelIdeal G.isBorel G.torusSplit G.split_surjective
      (G.borelRootBasis.coord i) ∈ G.rootSubsetIdeal R hR := by
  apply (HopfIdeal.mem_vanishingIdeal _ _).mpr
  intro g
  obtain ⟨u, hu, hval⟩ := Subgroup.mem_map.mp g.property
  have heq : u.val = g.val := hval
  rw [← heq]
  exact (borelRootLogarithmCoordinate_eval G.borelIdeal G.isBorel G.torusSplit
    G.split_surjective (G.borelRootBasis.coord i) u).trans (hu i hi)

/-- The tangent of a closed root support is spanned by its chosen root-map tangents. -/
theorem rootSubsetTangent_eq_span (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    (hopfTangentImage (G.rootSubsetIdeal R hR)).toSubmodule =
      Submodule.span K ((fun i => gaAffineGroupTangent (G.borelRootMaps i)) ''
        G.rootCharacters R) := by
  apply le_antisymm
  · intro d hd
    have hdU : d ∈ G.unipotentTangent :=
      hopfQuotient_tangentImage_antitone (G.rootSubsetIdeal R hR) G.unipotentIdeal
        (G.unipotentIdeal_le_rootSubset R hR) hd
    let v : G.unipotentTangent := ⟨d, hdU⟩
    have hc (i) (hi : i ∉ G.rootCharacters R) : G.borelRootBasis.coord i v = 0 := by
      have hdiff := borelRootLogarithmCoordinate_tangent G.borelIdeal G.isBorel G.torusSplit
        G.split_surjective (G.borelRootBasis.coord i) v
      have hzero := (tangent_mem_hopfQuotient_iff (G.rootSubsetIdeal R hR) d).mp hd _
        (G.logarithm_mem_rootIdeal R hR i hi)
      apply hdiff.symm.trans
      change Bialgebra.CounitAlgebra.algEquivSelf K G.coordinateAlgebra K (d _) = 0
      rw [hzero, map_zero]
    have hv : v ∈ Submodule.span K (G.borelRootBasis '' G.rootCharacters R) := by
      apply G.borelRootBasis.mem_span_image.mpr
      intro i hi
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hi) (hc i hn)
    have hmap := Submodule.mem_map_of_mem (f := G.unipotentTangent.toSubmodule.subtype) hv
    rw [Submodule.map_span] at hmap
    simpa only [Set.image_image, Function.comp_def, Submodule.subtype_apply,
      borelRootBasis_tangent] using hmap
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact G.rootMapTangent_mem_rootSubset R hR ⟨i, hi⟩

/-- A singleton positive root subgroup has exactly its one-dimensional root tangent space. -/
theorem singletonRootTangent (r : G.rootIndex) (hr : G.rootBase.IsPos r)
    (hR : IsPositiveRootClosed G.rootBase {r}) :
    (hopfTangentImage (G.rootSubsetIdeal {r} hR)).toSubmodule = G.rootWeightSpace r := by
  apply le_antisymm
  · rw [G.rootSubsetTangent_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi' : G.characterRootEquiv
        (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) = r := hi
    have hchar : G.rootCharacter r = i.val := by
      rw [← hi']
      change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val
      rw [Equiv.symm_apply_apply]
      rfl
    change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
    rw [hchar]
    exact G.borelRootMaps_weight i
  · exact G.rootWeightSpace_le_rootSubset {r} hR r hr (Set.mem_singleton r)

end ReductiveGroups.ReductiveGroupData
