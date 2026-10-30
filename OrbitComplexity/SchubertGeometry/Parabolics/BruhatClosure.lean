import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.SchubertGeometry.FlagVariety.PointTopology
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatClosure
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneCellClosure
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneSweepClosed
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-! # Bruhat order and Schubert closures

Rank-one root curves and closed sweeps identify the closure of each Bruhat double coset.
Passing to flags gives the decomposition of a Schubert variety into its lower cells.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry Topology ReductiveGroups TauCeti GroupActions
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem simple_one_mem_closure (i : G.rootBase.support) :
    (1 : G.points) ∈ closure (subgroupDoubleCoset G.borelPoints (G.reflectionPoint i.val)) := by
  exact one_mem_closure_pointDoubleCoset G.borelPoints (G.reflectionPoint i.val)
    (G.negativeSimpleRootMap i) (fun d hd =>
      (G.isBruhatSystem.rankOne i).y_mem_doubleCoset hd)

private theorem simple_sweep_closed (i : G.rootBase.support) (Y : Set G.points)
    (hY : IsClosed Y)
    (hrel : ∀ g c, c ≠ 0 →
      (g * gaParameterPoint (G.negativeSimpleRootMap i) c ∈ Y ↔
        g * gaParameterPoint (G.simpleRootMap i) c⁻¹ * G.reflectionPoint i.val ∈ Y)) :
    IsClosed (sweepSet (fun c => gaParameterPoint (G.negativeSimpleRootMap i) c)
      (G.reflectionPoint i.val) Y) :=
  isClosed_rankOneSweep Y hY (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    (G.reflectionPoint i.val) hrel

/-- A Bruhat double coset has exactly the lower double cosets in its closure. -/
theorem bruhat_doubleCoset_closure (w : G.weylGroup) :
    closure (subgroupDoubleCoset G.borelPoints (G.weylPoint w)) =
      ⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase v w),
        subgroupDoubleCoset G.borelPoints (G.weylPoint v) := by
  simp only [G.weylPoint_eq]
  apply le_antisymm
  · exact G.isBruhatSystem.closure_doubleCoset_subset (isClosed_borelPoints G)
      (simple_sweep_closed G) w
  · intro g hg
    obtain ⟨v, hv, hgv⟩ := Set.mem_iUnion₂.mp hg
    exact G.isBruhatSystem.doubleCoset_subset_closure_of_le
      (simple_one_mem_closure G) hv hgv

private theorem cell_preimage (w : G.weylGroup) :
    (flagVarietyPointsHomeomorph G) ⁻¹'
      Set.range (Variety.mapPoints (schubertCellInclusion G w)) =
        flagProjection G '' subgroupDoubleCoset G.borelPoints (G.weylPoint w) := by
  ext q
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  rw [Set.mem_preimage, schubertCell_points_range]
  change flagVarietyPointsEquiv G (flagProjection G g) ∈ _ ↔ _
  rw [mem_schubertOrbit_iff]
  constructor
  · exact fun h => ⟨g, h, rfl⟩
  · rintro ⟨g', hg', he⟩
    have hb := (flagProjection_eq_iff G g' g).mp he
    have hm := subgroupDoubleCoset_mul_mem hg' hb
    simpa only [mul_inv_cancel_left] using hm

private theorem schubert_closure_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (schubertInclusion G w)) =
      closure (Set.range (Variety.mapPoints (schubertCellInclusion G w))) := by
  rw [(flagVariety G).isEmbedding_pointMap.closure_eq_preimage_closure_image]
  change _ = (flagVariety G).pointMap ⁻¹' (flagVariety G).pointClosure _
  rw [(schubertCell G w).pointClosure_range, Variety.range_mapPoints,
    schubertInclusion_range]

/-- The rational points of a Schubert variety are the cells below its Weyl element. -/
theorem schubertVariety_points_cells (w : G.weylGroup) :
    Set.range (Variety.mapPoints (schubertInclusion G w)) =
      ⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase v w),
        Set.range (Variety.mapPoints (schubertCellInclusion G v)) := by
  have hc : (flagVarietyPointsHomeomorph G) ⁻¹'
      Set.range (Variety.mapPoints (schubertInclusion G w)) =
      (flagVarietyPointsHomeomorph G) ⁻¹'
        (⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase v w),
          Set.range (Variety.mapPoints (schubertCellInclusion G v))) := by
    rw [schubert_closure_points, Homeomorph.preimage_closure, cell_preimage,
      closure_image_mk_eq, subgroupDoubleCoset_mul_subgroup, bruhat_doubleCoset_closure,
      Set.image_iUnion]
    simp only [Set.preimage_iUnion, cell_preimage, Set.image_iUnion]
  exact (Set.preimage_injective.mpr (flagVarietyPointsHomeomorph G).surjective) hc

/-- A Weyl flag belongs to a Schubert variety exactly when its index lies below it. -/
theorem weylFlag_mem_schubert_iff (v w : G.weylGroup) :
    weylFlagPoint G v ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) ↔
      WeylBruhatLE G.rootBase v w := by
  rw [schubertVariety_points_cells]
  constructor
  · intro hv
    obtain ⟨a, ha, hva⟩ := Set.mem_iUnion₂.mp hv
    have hvv : weylFlagPoint G v ∈
        Set.range (Variety.mapPoints (schubertCellInclusion G v)) := by
      rw [schubertCell_points_range]
      exact MulAction.mem_orbit_self _
    rw [schubertCell_points_range] at hva hvv
    exact schubertOrbits_disjoint G hvv hva ▸ ha
  · intro hvw
    apply Set.mem_iUnion₂.mpr
    refine ⟨v, hvw, ?_⟩
    rw [schubertCell_points_range]
    exact MulAction.mem_orbit_self _

end SchubertGeometry
