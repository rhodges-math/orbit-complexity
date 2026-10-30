import OrbitComplexity.SchubertGeometry.Cells.RootChart
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootProducts
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent

/-! # Root factors of Borel points

Inversion roots and their positive complements give the unipotent factors of a Borel point.
-/

open ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem borelFactorization (b : G.points) (hb : b ∈ G.borelPoints) :
    ∃ u ∈ G.unipotentPoints, ∃ t ∈ G.torusPoints, u * t = b := by
  obtain ⟨t, ht, u, hu, he⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive b⁻¹ (G.borelPoints.inv_mem hb)
  refine ⟨u⁻¹, G.unipotentPoints.inv_mem hu, t⁻¹, G.torusPoints.inv_mem ht, ?_⟩
  simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he

private theorem fullRootPoints (u : G.points) (hu : u ∈ G.unipotentPoints) :
    u ∈ G.rootSubsetPoints {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) := by
  rw [G.rootSubsetPoints_eq]
  apply Subgroup.mem_map.mpr
  refine ⟨⟨u, hu⟩, ?_, rfl⟩
  change ∀ i, i ∉ G.rootCharacters {r | G.rootBase.IsPos r} → _
  intro i hi
  exact (hi (G.borelCharacterRootEquiv i).property).elim

private theorem unipotentFactors (w : G.weylGroup) (u : G.points) (hu : u ∈ G.unipotentPoints) :
    ∃ u₁ ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w),
      ∃ u₂ ∈ G.rootSubsetPoints
          {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase w}
          (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w), u₁ * u₂ = u := by
  have hunion : {r | G.rootBase.IsPos r} = leftRootInversionIndices G.rootBase w ∪
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase w} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_union, mem_leftRootInversionIndices]
    tauto
  have hdisj : Disjoint (leftRootInversionIndices G.rootBase w)
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase w} := by
    apply Set.disjoint_left.mpr
    intro r hr hn
    exact hn.2 hr
  obtain ⟨p, hp, _⟩ := G.rootSubsetPoints_existsUnique_mul _ _ _
    (isPositiveRootClosed_isPos G.rootBase)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w) hunion hdisj u
    (fullRootPoints G u hu)
  exact ⟨p.1, hp.1, p.2, hp.2.1, hp.2.2⟩

/-- A Borel point factors into its inversion-root, complementary-root and torus factors. -/
theorem borelRootFactorization (w : G.weylGroup) (b : G.points) (hb : b ∈ G.borelPoints) :
    ∃ u₁ ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w),
      ∃ u₂ ∈ G.rootSubsetPoints
          {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase w}
          (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w),
        ∃ t ∈ G.torusPoints, u₁ * u₂ * t = b := by
  obtain ⟨u, hu, t, ht, he⟩ := borelFactorization G b hb
  obtain ⟨u₁, hu₁, u₂, hu₂, hprod⟩ := unipotentFactors G w u hu
  refine ⟨u₁, hu₁, u₂, hu₂, t, ht, ?_⟩
  rw [hprod, he]

end
end SchubertGeometry
