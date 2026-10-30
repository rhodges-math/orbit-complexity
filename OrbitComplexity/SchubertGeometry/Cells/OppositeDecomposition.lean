import OrbitComplexity.SchubertGeometry.Cells.Decomposition
import OrbitComplexity.SchubertGeometry.Cells.Stability

/-! # The opposite Schubert decomposition

Translation by the longest representative identifies opposite Borel orbits with Borel orbits.
Constructibility extends rational-point coverage and disjointness to all scheme points.
-/

open ReductiveGroups AlgebraicGeometry Topology
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem longestInverseProduct (w : G.weylGroup) :
    ∃ t ∈ G.torusPoints, G.longestPoint⁻¹ * G.weylPoint w =
      t * G.weylPoint (G.longestElement⁻¹ * w) := by
  obtain ⟨a, ha, hia⟩ := G.isBruhatSystem.weyl.weylElementPoint_inv
    G.rootBase G.longestElement
  have hi : G.longestPoint⁻¹ = a * G.weylPoint G.longestElement⁻¹ := by
    simpa only [ReductiveGroupData.longestPoint, G.weylPoint_eq] using hia
  obtain ⟨b, hb, hmb⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul
    G.rootBase G.longestElement⁻¹ w
  have hm : G.weylPoint G.longestElement⁻¹ * G.weylPoint w =
      b * G.weylPoint (G.longestElement⁻¹ * w) := by
    simpa only [G.weylPoint_eq] using hmb
  exact ⟨a * b, G.torusPoints.mul_mem ha hb, by rw [hi, mul_assoc, hm, mul_assoc]⟩

private theorem opposite_to_borel (b : G.points) (hb : b ∈ G.oppositeBorelPoints) :
    G.longestPoint⁻¹ * b * G.longestPoint ∈ G.borelPoints := by
  apply (G.conj_mem_oppositeBorel _).mp
  have he : G.longestPoint * (G.longestPoint⁻¹ * b * G.longestPoint) *
      G.longestPoint⁻¹ = b := by group
  rwa [he]

/-- Longest translation tests an opposite Borel orbit by an ordinary Bruhat double coset. -/
theorem mem_oppositeOrbit_iff (w : G.weylGroup) (g : G.points) :
    flagVarietyPointsEquiv G (flagProjection G g) ∈
      MulAction.orbit (GroupActions.oppositeBorelVariety G).points (weylFlagPoint G w) ↔
    G.longestPoint⁻¹ * g ∈ subgroupDoubleCoset G.borelPoints
      (G.weylPoint (G.longestElement⁻¹ * w)) := by
  obtain ⟨t, ht, hnt⟩ := longestInverseProduct G w
  constructor
  · intro hg
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hg
    rw [weylFlagPoint, oppositeBorelFlag_smul] at hb
    have he := (flagVarietyPointsEquiv G).injective hb
    let bm : G.points := GroupActions.oppositeBorelPointsMulEquiv G b
    let c := (bm * G.weylPoint w)⁻¹ * g
    have hc : c ∈ G.borelPoints := (flagProjection_eq_iff G _ _).mp he
    let bs := G.longestPoint⁻¹ * bm * G.longestPoint
    have hbs : bs ∈ G.borelPoints :=
      opposite_to_borel G bm (GroupActions.oppositeBorelPointsMulEquiv G b).property
    refine ⟨bs * t, G.borelPoints.mul_mem hbs (G.torus_le_borel ht), c, hc, ?_⟩
    calc
      G.longestPoint⁻¹ * g = bs * ((G.longestPoint⁻¹ * G.weylPoint w) * c) := by
        dsimp only [bs, c]
        group
      _ = _ := by rw [hnt]; group
  · rintro ⟨b, hb, c, hc, he⟩
    let bm := G.longestPoint * (b * t⁻¹) * G.longestPoint⁻¹
    have hbm : bm ∈ G.oppositeBorelPoints :=
      (G.conj_mem_oppositeBorel _).mpr
        (G.borelPoints.mul_mem hb (G.torus_le_borel (G.torusPoints.inv_mem ht)))
    have hg : g = G.longestPoint * (b * G.weylPoint (G.longestElement⁻¹ * w) * c) := by
      rw [← he]
      group
    have hweyl : G.weylPoint (G.longestElement⁻¹ * w) =
        t⁻¹ * (G.longestPoint⁻¹ * G.weylPoint w) := by rw [hnt]; group
    have hfactor : g = bm * G.weylPoint w * c := by
      rw [hg, hweyl]
      dsimp only [bm]
      group
    let p := (GroupActions.oppositeBorelPointsMulEquiv G).symm ⟨bm, hbm⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨p, ?_⟩
    rw [weylFlagPoint, oppositeBorelFlag_smul]
    apply congrArg (flagVarietyPointsEquiv G)
    change flagProjection G ((GroupActions.oppositeBorelPointsMulEquiv G p : G.points) *
      G.weylPoint w) = flagProjection G g
    have hp : (GroupActions.oppositeBorelPointsMulEquiv G p : G.points) = bm :=
      congrArg Subtype.val ((GroupActions.oppositeBorelPointsMulEquiv G).apply_symm_apply _)
    rw [hp, hfactor]
    apply (flagProjection_eq_iff G _ _).mpr
    simpa only [inv_mul_cancel_left] using hc

/-- Every rational flag belongs to an opposite Schubert cell. -/
theorem oppositeSchubertOrbits_cover (x : (flagVariety G).points) :
    ∃ w : G.weylGroup, x ∈ MulAction.orbit
      (GroupActions.oppositeBorelVariety G).points (weylFlagPoint G w) := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  obtain ⟨v, hv⟩ := bruhatDecomposition G (G.longestPoint⁻¹ * g)
  refine ⟨G.longestElement * v, (mem_oppositeOrbit_iff G _ g).mpr ?_⟩
  simpa only [inv_mul_cancel_left] using hv

/-- A rational flag lies in at most one opposite Schubert cell. -/
theorem oppositeSchubertOrbits_disjoint {v w : G.weylGroup} {x : (flagVariety G).points}
    (hv : x ∈ MulAction.orbit (GroupActions.oppositeBorelVariety G).points (weylFlagPoint G v))
    (hw : x ∈ MulAction.orbit (GroupActions.oppositeBorelVariety G).points (weylFlagPoint G w)) :
    v = w := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  have h := bruhatDecomposition_unique G ((mem_oppositeOrbit_iff G v g).mp hv)
    ((mem_oppositeOrbit_iff G w g).mp hw)
  exact mul_left_cancel h

private theorem oppositeCellUnion_eq_univ :
    (⋃ w : G.weylGroup, Set.range (oppositeSchubertCellInclusion G w).left) = Set.univ := by
  let := weylGroup_finite G.rootBase
  have : JacobsonSpace (flagVariety G).toOver.left := by
    change JacobsonSpace (flagVariety G).scheme
    exact LocallyOfFiniteType.jacobsonSpace (flagVariety G).toSpec
  apply GroupActions.constructible_eq
    (IsConstructible.iUnion (fun w =>
      GroupActions.Variety.isConstructible_range (oppositeSchubertCellInclusion G w))) .univ
  ext p
  constructor
  · rintro ⟨_, hp⟩
    exact ⟨Set.mem_univ p, hp⟩
  · rintro ⟨_, hp⟩
    have hp' : p ∈ Set.range (flagVariety G).pointMap := by
      rw [GroupActions.Variety.pointMap_range]
      exact hp
    obtain ⟨x, rfl⟩ := hp'
    obtain ⟨w, hw⟩ := oppositeSchubertOrbits_cover G x
    rw [← oppositeSchubertCell_points_range] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨Set.mem_iUnion.mpr ⟨w, ?_⟩, hp⟩
    refine ⟨(oppositeSchubertCell G w).pointMap z, ?_⟩
    rw [← GroupActions.Variety.pointMap_mapPoints, hz]

/-- Every scheme point belongs to an opposite Schubert cell. -/
theorem oppositeSchubertCells_cover (x : (flagVariety G).scheme) :
    ∃ w : G.weylGroup, x ∈ Set.range (oppositeSchubertCellInclusion G w).left := by
  apply Set.mem_iUnion.mp
  rw [oppositeCellUnion_eq_univ]
  exact Set.mem_univ x

/-- Opposite Schubert cells containing the same scheme point have equal Weyl indices. -/
theorem oppositeSchubertCells_disjoint {v w : G.weylGroup} {x : (flagVariety G).scheme}
    (hv : x ∈ Set.range (oppositeSchubertCellInclusion G v).left)
    (hw : x ∈ Set.range (oppositeSchubertCellInclusion G w).left) : v = w := by
  have : JacobsonSpace (flagVariety G).toOver.left := by
    change JacobsonSpace (flagVariety G).scheme
    exact LocallyOfFiniteType.jacobsonSpace (flagVariety G).toSpec
  obtain ⟨p, hp, hclosed⟩ := GroupActions.constructible_closedPoint
    ((GroupActions.Variety.isConstructible_range (oppositeSchubertCellInclusion G v)).inter
      (GroupActions.Variety.isConstructible_range (oppositeSchubertCellInclusion G w))) ⟨x, hv, hw⟩
  have hp' : p ∈ Set.range (flagVariety G).pointMap := by
    rw [GroupActions.Variety.pointMap_range]
    exact hclosed
  obtain ⟨q, rfl⟩ := hp'
  obtain ⟨a, ha⟩ := GroupActions.Variety.exists_mapPoints_eq
    (oppositeSchubertCellInclusion G v) q hp.1
  obtain ⟨b, hb⟩ := GroupActions.Variety.exists_mapPoints_eq
    (oppositeSchubertCellInclusion G w) q hp.2
  apply oppositeSchubertOrbits_disjoint G (x := q)
  · rw [← oppositeSchubertCell_points_range]
    exact ⟨a, ha⟩
  · rw [← oppositeSchubertCell_points_range]
    exact ⟨b, hb⟩

end
end SchubertGeometry
