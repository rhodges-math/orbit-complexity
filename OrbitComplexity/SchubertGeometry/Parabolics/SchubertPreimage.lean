import OrbitComplexity.SchubertGeometry.Parabolics.CellProducts
import OrbitComplexity.SchubertGeometry.Parabolics.Order
import OrbitComplexity.SchubertGeometry.Parabolics.PartialPoints
import OrbitComplexity.SchubertGeometry.Parabolics.Stabilizer

/-!
# Partial Schubert point preimages

The quotient projection identifies partial Schubert closures with full Schubert closures
whose index has the longest parabolic suffix.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The rational partial Schubert set is the closure of its Borel orbit. -/
def partialSchubertPoints (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set (partialFlagPoints G J) :=
  closure (MulAction.orbit G.borelPoints
    (partialFlagProjection G J (flagProjection G (G.weylPoint w))))

private theorem orbit_image (J : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbit G.borelPoints
        (partialFlagProjection G J (flagProjection G (G.weylPoint w))) =
      (QuotientGroup.mk : G.points → partialFlagPoints G J) ''
        subgroupDoubleCoset G.borelPoints (G.weylPoint w) := by
  ext q
  constructor
  · intro hq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
    change (QuotientGroup.mk ((b : G.points) * G.weylPoint w) : partialFlagPoints G J) = q at hb
    refine ⟨(b : G.points) * G.weylPoint w,
      ⟨b, b.property, 1, G.borelPoints.one_mem, by simp⟩, ?_⟩
    exact hb
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk (b * G.weylPoint w) : partialFlagPoints G J) =
      QuotientGroup.mk (b * G.weylPoint w * c)
    apply QuotientGroup.eq.mpr
    have he : (b * G.weylPoint w)⁻¹ * (b * G.weylPoint w * c) = c := by group
    rw [he]
    exact (le_sup_left : G.borelPoints ≤ standardParabolicPoints G J) hc

private theorem parabolic_closure_eq (J : Set G.rootBase.support) :
    (standardParabolicPoints G J : Set G.points) = closure
      (subgroupDoubleCoset G.borelPoints (G.weylPoint (longestParabolicElement G.rootBase J))) := by
  rw [(standardParabolicPoints_bruhat G J).1,
    bruhat_doubleCoset_closure G (longestParabolicElement G.rootBase J)]
  simp only [weylParabolic_bruhat_iff G.rootBase J]

omit [IsAlgClosed K] [CharZero K] in
private theorem closure_mul_closure (A B : Set G.points) :
    closure (A * closure B) = closure (A * B) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact map_mem_closure SeparatelyContinuousMul.continuous_const_mul hb
      (fun y hy => ⟨a, ha, y, hy, rfl⟩)
  · apply closure_mono
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, subset_closure hb, rfl⟩

private theorem group_preimage (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (QuotientGroup.mk : G.points → partialFlagPoints G J) ⁻¹' partialSchubertPoints G J w =
      closure (subgroupDoubleCoset G.borelPoints
        (G.weylPoint (w * longestParabolicElement G.rootBase J))) := by
  have hcont : Continuous (QuotientGroup.mk : G.points → partialFlagPoints G J) :=
    continuous_quot_mk
  have hopen := QuotientGroup.isOpenMap_coe (N := standardParabolicPoints G J)
  rw [partialSchubertPoints, orbit_image G J w,
    hopen.preimage_closure_eq_closure_preimage hcont,
    QuotientGroup.preimage_image_mk_eq_mul, parabolic_closure_eq G J, closure_mul_closure G,
    minimal_parabolic_cell_mul G J w _ hw (longestParabolicElement_mem G.rootBase J)]

private theorem groupFlag_mem_closure (w : G.weylGroup) (g : G.points) :
    flagVarietyPointsEquiv G (flagProjection G g) ∈
        Set.range (Variety.mapPoints (schubertInclusion G w)) ↔
      g ∈ closure (subgroupDoubleCoset G.borelPoints (G.weylPoint w)) := by
  rw [schubertVariety_points_cells G w, bruhat_doubleCoset_closure G w]
  simp only [Set.mem_iUnion, schubertCell_points_range, mem_schubertOrbit_iff]

/-- The partial Schubert preimage is the full Schubert set with longest parabolic suffix. -/
theorem partialSchubert_preimage (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (partialFlagProjection G J) ⁻¹' partialSchubertPoints G J w =
      (flagVarietyPointsEquiv G) ⁻¹' Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J))) := by
  apply (Set.preimage_injective.mpr (flagProjection_surjective G))
  ext g
  change g ∈ (QuotientGroup.mk : G.points → partialFlagPoints G J) ⁻¹'
    partialSchubertPoints G J w ↔ _
  rw [group_preimage G J w hw]
  exact (groupFlag_mem_closure G (w * longestParabolicElement G.rootBase J) g).symm

/-- Weyl flags in a partial Schubert closure are detected by their minimal representatives. -/
theorem partialSchubert_weyl_iff (J : Set G.rootBase.support) (w u : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    partialFlagProjection G J (flagProjection G (G.weylPoint u)) ∈ partialSchubertPoints G J w ↔
      WeylBruhatLE G.rootBase (rightParabolicRepresentative G.rootBase J u) w := by
  change flagProjection G (G.weylPoint u) ∈
    (partialFlagProjection G J) ⁻¹' partialSchubertPoints G J w ↔ _
  rw [partialSchubert_preimage G J w hw]
  change weylFlagPoint G u ∈ Set.range (Variety.mapPoints
    (schubertInclusion G (w * longestParabolicElement G.rootBase J))) ↔ _
  rw [weylFlag_mem_schubert_iff G u (w * longestParabolicElement G.rootBase J)]
  exact weylParabolic_saturation G.rootBase J w u hw

/-- The stabilizer of a rational partial Schubert closure is its longest-suffix parabolic. -/
theorem partialSchubert_stabilizer (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    MulAction.stabilizer G.points (partialSchubertPoints G J w) = standardParabolicPoints G
      (BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
        (w * longestParabolicElement G.rootBase J)) := by
  calc
    _ = MulAction.stabilizer G.points
        ((partialFlagProjection G J) ⁻¹' partialSchubertPoints G J w) :=
      (stabilizer_preimage_of_surjective (partialFlagProjection G J)
        (partialFlagProjection_surjective G J) (partialFlagProjection_smul G J) _).symm
    _ = schubertStabilizer G (w * longestParabolicElement G.rootBase J) := by
      rw [partialSchubert_preimage G J w hw]
      rfl
    _ = _ := schubertStabilizer_eq G (w * longestParabolicElement G.rootBase J)

end SchubertGeometry
