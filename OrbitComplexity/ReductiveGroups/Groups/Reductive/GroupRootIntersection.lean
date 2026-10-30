import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootConjugation
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootProducts

/-!
# Root groups as intersections of unipotent subgroups

The full positive support gives the unipotent subgroup. Splitting its root support
into inversions and positive noninversions, then conjugating by a Weyl representative,
identifies the inversion-root subgroup with the intersection of the unipotent group
and the Weyl-conjugated opposite unipotent group.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- All positive roots give the full unipotent point subgroup. -/
theorem fullRootPoints_eq_unipotent :
    G.rootSubsetPoints {r | G.rootBase.IsPos r} (isPositiveRootClosed_isPos G.rootBase) =
      G.unipotentPoints := by
  apply le_antisymm (G.rootSubsetPoints_le_unipotent _ _)
  intro u hu
  rw [G.rootSubsetPoints_eq]
  apply Subgroup.mem_map.mpr
  refine ⟨⟨u, hu⟩, ?_, rfl⟩
  change ∀ i, i ∉ G.rootCharacters {r | G.rootBase.IsPos r} → _
  intro i hi
  exact (hi (G.borelCharacterRootEquiv i).property).elim

/-- Inversion-root points are the unipotent points conjugated into the opposite group. -/
theorem mem_inversionPoints_iff (w : G.weylGroup) (g : G.points) :
    g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ↔
      g ∈ G.unipotentPoints ∧
        (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.oppositeUnipotentPoints := by
  constructor
  · intro hg
    exact ⟨G.rootSubsetPoints_le_unipotent _ _ hg, G.inversionPoints_conj_opposite w g hg⟩
  · rintro ⟨hu, hop⟩
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
    have hfull : g ∈ G.rootSubsetPoints {r | G.rootBase.IsPos r}
        (isPositiveRootClosed_isPos G.rootBase) := by
      rwa [G.fullRootPoints_eq_unipotent]
    obtain ⟨p, ⟨hp₁, hp₂, hprod⟩, _⟩ := G.rootSubsetPoints_existsUnique_mul _ _ _
      (isPositiveRootClosed_isPos G.rootBase)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w) hunion hdisj g hfull
    have hp₁op := G.inversionPoints_conj_opposite w p.1 hp₁
    have hp₂op : (G.weylPoint w)⁻¹ * p.2 * G.weylPoint w ∈
        G.oppositeUnipotentPoints := by
      have h := G.oppositeUnipotentPoints.mul_mem
        (G.oppositeUnipotentPoints.inv_mem hp₁op) hop
      rw [← hprod] at h
      convert h using 1
      group
    have hp₂B := G.unipotent_le_borel (G.noninversionPoints_conj_unipotent w p.2 hp₂)
    have hc := G.eq_one_of_oppositeUnipotent_borel _ hp₂op hp₂B
    have hp₂one : p.2 = 1 := by
      have h := congrArg (fun z : G.points => G.weylPoint w * z * (G.weylPoint w)⁻¹) hc
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h
    have hfirst : p.1 = g := by simpa only [hp₂one, mul_one] using hprod
    exact hfirst ▸ hp₁

/-- The inversion-root subgroup is the intersection with the Weyl-conjugated opposite subgroup. -/
theorem inversionPoints_eq_inter (w : G.weylGroup) :
    G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      G.unipotentPoints ⊓ G.oppositeUnipotentPoints.map
        (MulAut.conj (G.weylPoint w)).toMonoidHom := by
  ext g
  rw [G.mem_inversionPoints_iff]
  constructor
  · rintro ⟨hU, hop⟩
    refine ⟨hU, Subgroup.mem_map.mpr ⟨(G.weylPoint w)⁻¹ * g * G.weylPoint w, hop, ?_⟩⟩
    change G.weylPoint w * ((G.weylPoint w)⁻¹ * g * G.weylPoint w) *
      (G.weylPoint w)⁻¹ = g
    group
  · rintro ⟨hU, hop⟩
    obtain ⟨v, hv, he⟩ := Subgroup.mem_map.mp hop
    change G.weylPoint w * v * (G.weylPoint w)⁻¹ = g at he
    refine ⟨hU, ?_⟩
    rw [← he]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_inv_cancel, mul_one] using hv

end ReductiveGroups.ReductiveGroupData
