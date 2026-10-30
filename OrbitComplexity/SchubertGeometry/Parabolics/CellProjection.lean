import OrbitComplexity.SchubertGeometry.Parabolics.SchubertPreimage

/-! # Schubert cell projections to parabolic cosets

A minimum right representative gives a bijection of rational Schubert cells under the
parabolic projection. The full Schubert closure maps onto the corresponding partial closure.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem cell_representative (w : G.weylGroup) (q : flagPoints G)
    (hq : flagVarietyPointsEquiv G q ∈
      Set.range (Variety.mapPoints (schubertCellInclusion G w))) :
    ∃ b ∈ G.borelPoints, flagProjection G (b * G.weylPoint w) = q := by
  rw [schubertCell_points_range G w] at hq
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
  rw [weylFlagPoint, borelFlag_smul G] at hb
  exact ⟨borelPointsMulEquiv G b, (borelPointsMulEquiv G b).property,
    (flagVarietyPointsEquiv G).injective hb⟩

private theorem borel_conjugate (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) (b : G.points) (hb : b ∈ G.borelPoints)
    (hp : (G.weylPoint w)⁻¹ * b * G.weylPoint w ∈ standardParabolicPoints G J) :
    (G.weylPoint w)⁻¹ * b * G.weylPoint w ∈ G.borelPoints := by
  change (G.weylPoint w)⁻¹ * b * G.weylPoint w ∈
    (standardParabolicPoints G J : Set G.points) at hp
  rw [(standardParabolicPoints_bruhat G J).1] at hp
  obtain ⟨a, ha, hpa⟩ := Set.mem_iUnion₂.mp hp
  have hn : G.weylPoint w ∈ subgroupDoubleCoset G.borelPoints (G.weylPoint w) :=
    ⟨1, G.borelPoints.one_mem, 1, G.borelPoints.one_mem, by simp⟩
  have hm := Set.mul_mem_mul hn hpa
  rw [minimal_parabolic_cell_mul G J w a hw ha] at hm
  have he : G.weylPoint w * ((G.weylPoint w)⁻¹ * b * G.weylPoint w) =
      b * G.weylPoint w := by group
  rw [he] at hm
  have hbcell : b * G.weylPoint w ∈
      subgroupDoubleCoset G.borelPoints (G.weylPoint w) :=
    ⟨b, hb, 1, G.borelPoints.one_mem, by simp⟩
  have haa : a = 1 := by
    have hwa := bruhatDecomposition_unique G hm hbcell
    exact mul_left_cancel (hwa.trans (mul_one w).symm)
  subst a
  obtain ⟨c, hc, d, hd, hcd⟩ := hpa
  have hn1 : G.weylPoint (1 : G.weylGroup) ∈ G.borelPoints :=
    by
      rw [G.weylPoint_eq, weylElementPoint_one]
      exact G.borelPoints.one_mem
  rw [hcd]
  exact G.borelPoints.mul_mem (G.borelPoints.mul_mem hc hn1) hd

/-- A full Schubert cell projects onto the corresponding partial Borel orbit. -/
theorem partialFlagProjection_cell (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialFlagProjection G J) '' ((flagVarietyPointsEquiv G) ⁻¹'
      Set.range (Variety.mapPoints (schubertCellInclusion G w))) =
      MulAction.orbit G.borelPoints
        (partialFlagProjection G J (flagProjection G (G.weylPoint w))) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨b, hb, rfl⟩ := cell_representative G w p hp
    exact MulAction.mem_orbit_iff.mpr ⟨⟨b, hb⟩, rfl⟩
  · intro hq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
    refine ⟨flagProjection G ((b : G.points) * G.weylPoint w), ?_, hb⟩
    change flagVarietyPointsEquiv G
      (flagProjection G ((b : G.points) * G.weylPoint w)) ∈
        Set.range (Variety.mapPoints (schubertCellInclusion G w))
    rw [schubertCell_points_range G w]
    exact (mem_schubertOrbit_iff G w _).mpr
      ⟨b, b.property, 1, G.borelPoints.one_mem, by simp⟩

/-- A minimum right representative gives injectivity on its full Schubert cell. -/
theorem partialFlagProjection_injOn (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    Set.InjOn (partialFlagProjection G J) ((flagVarietyPointsEquiv G) ⁻¹'
      Set.range (Variety.mapPoints (schubertCellInclusion G w))) := by
  intro p hp q hq heq
  obtain ⟨b, hb, rfl⟩ := cell_representative G w p hp
  obtain ⟨c, hc, rfl⟩ := cell_representative G w q hq
  have hm := (partialFlagProjection_eq G J _ _).mp heq
  have hinv : (b * G.weylPoint w)⁻¹ * (c * G.weylPoint w) =
      (G.weylPoint w)⁻¹ * (b⁻¹ * c) * G.weylPoint w := by group
  rw [hinv] at hm
  apply (flagProjection_eq_iff G _ _).mpr
  rw [hinv]
  exact borel_conjugate G J w hw (b⁻¹ * c)
    (G.borelPoints.mul_mem (G.borelPoints.inv_mem hb) hc) hm

/-- A full Schubert closure projects onto the corresponding partial Schubert closure. -/
theorem partialSchubert_image (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (partialFlagProjection G J) '' ((flagVarietyPointsEquiv G) ⁻¹'
      Set.range (Variety.mapPoints (schubertInclusion G w))) = partialSchubertPoints G J w := by
  have htop : WeylBruhatLE G.rootBase w (w * longestParabolicElement G.rootBase J) := by
    apply (weylParabolic_saturation G.rootBase J w w hw).mpr
    rw [rightParabolicRepresentative_of_minimal G.rootBase J w hw]
    exact WeylBruhatLE.refl G.rootBase w
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hptop : flagVarietyPointsEquiv G p ∈ Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J))) := by
      rw [schubertVariety_points_cells G w] at hp
      obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp hp
      rw [schubertVariety_points_cells G (w * longestParabolicElement G.rootBase J)]
      exact Set.mem_iUnion₂.mpr ⟨v, hv.trans htop, hpv⟩
    change p ∈ (partialFlagProjection G J) ⁻¹' partialSchubertPoints G J w
    rw [partialSchubert_preimage G J w hw]
    exact hptop
  · intro hq
    obtain ⟨p, rfl⟩ := partialFlagProjection_surjective G J q
    have hp : flagVarietyPointsEquiv G p ∈ Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J))) := by
      change p ∈ (flagVarietyPointsEquiv G) ⁻¹' Set.range (Variety.mapPoints
        (schubertInclusion G (w * longestParabolicElement G.rootBase J)))
      rw [← partialSchubert_preimage G J w hw]
      exact hq
    rw [schubertVariety_points_cells G (w * longestParabolicElement G.rootBase J)] at hp
    obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp hp
    have hr := (weylParabolic_saturation G.rootBase J w v hw).mp hv
    have hcoset : partialFlagProjection G J (flagProjection G (G.weylPoint v)) =
        partialFlagProjection G J
          (flagProjection G (G.weylPoint (rightParabolicRepresentative G.rootBase J v))) := by
      apply (partialWeylFlag_eq_iff G J v _).mpr
      have he := congrArg (fun z : G.weylGroup =>
        z⁻¹ * rightParabolicRepresentative G.rootBase J v)
        (rightParabolic_factorization G.rootBase J v)
      have he' : v⁻¹ * rightParabolicRepresentative G.rootBase J v =
          (rightParabolicFactor G.rootBase J v)⁻¹ := by
        simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using he
      rw [he']
      exact (standardParabolicSubgroup G.rootBase J).inv_mem
        (rightParabolicFactor_mem G.rootBase J v)
    have hporbit : partialFlagProjection G J p ∈ MulAction.orbit G.borelPoints
        (partialFlagProjection G J (flagProjection G (G.weylPoint v))) := by
      rw [← partialFlagProjection_cell G J v]
      exact ⟨p, hpv, rfl⟩
    rw [hcoset, ← partialFlagProjection_cell G J
      (rightParabolicRepresentative G.rootBase J v)] at hporbit
    obtain ⟨r, hrcell, hre⟩ := hporbit
    refine ⟨r, ?_, hre⟩
    change flagVarietyPointsEquiv G r ∈ Set.range (Variety.mapPoints (schubertInclusion G w))
    rw [schubertVariety_points_cells G w]
    exact Set.mem_iUnion₂.mpr ⟨_, hr, hrcell⟩

end SchubertGeometry
