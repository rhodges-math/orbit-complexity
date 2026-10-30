import OrbitComplexity.SchubertGeometry.Cells.Stability

/-! # Stability of Schubert closures and Richardson intersections

Translations preserve orbit closures. The torus therefore preserves both Schubert closures
and their closed and locally closed Richardson intersections.
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem orbitClosure_stable (H X : GroupActions.Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (h : H.points) (x y : X.points)
    (hy : X.pointMap y ∈ GroupActions.orbitClosure H X x) :
    X.pointMap (h • y) ∈ GroupActions.orbitClosure H X x := by
  let e := GroupActions.Variety.translationIso H X h
  have hmapp (a : X.points) : GroupActions.Variety.mapPoints e.hom a = h • a :=
    GroupActions.Variety.mapPoints_translateMorphism H X h a
  have hm : GroupActions.Variety.mapPoints e.hom '' MulAction.orbit H.points x =
      MulAction.orbit H.points x := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hmapp]
      exact MulAction.mem_orbit_of_mem_orbit h ha
    · intro hz
      refine ⟨h⁻¹ • z, MulAction.mem_orbit_of_mem_orbit h⁻¹ hz, ?_⟩
      rw [hmapp, smul_inv_smul]
  have he := X.pointClosure_image e (MulAction.orbit H.points x)
  rw [hm] at he
  rw [← GroupActions.Variety.mapPoints_translateMorphism H X h y,
    GroupActions.Variety.pointMap_mapPoints]
  exact he.symm.le ⟨X.pointMap y, hy, rfl⟩

/-- The rational image of a Schubert variety is stable under its Borel action. -/
theorem schubertVariety_stable (w : G.weylGroup) (b : (GroupActions.borelVariety G).points)
    {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w))) :
    b • x ∈ Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w)) := by
  rw [GroupActions.Variety.range_mapPoints, schubertInclusion_range,
    GroupActions.orbitInclusion_range, ← GroupActions.orbitClosure_eq] at hx ⊢
  exact orbitClosure_stable _ _ b _ x hx

/-- The rational image of an opposite Schubert variety is opposite Borel stable. -/
theorem oppositeSchubertVariety_stable (w : G.weylGroup)
    (b : (GroupActions.oppositeBorelVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w))) :
    b • x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w)) := by
  rw [GroupActions.Variety.range_mapPoints, oppositeSchubertInclusion_range,
    GroupActions.orbitInclusion_range, ← GroupActions.orbitClosure_eq] at hx ⊢
  exact orbitClosure_stable _ _ b _ x hx

/-- The rational image of a Schubert variety is stable under the torus. -/
theorem schubertVariety_torus_stable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w)) := by
  let b := (GroupActions.borelPointsMulEquiv G).symm
    ⟨GroupActions.torusPointsMulEquiv G t,
      G.torus_le_borel (GroupActions.torusPointsMulEquiv G t).property⟩
  have he : t • x = b • x := by
    obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
    rw [torusFlag_smul, borelFlag_smul, MulEquiv.apply_symm_apply]
  rw [he]
  exact schubertVariety_stable G w b hx

/-- The rational image of an opposite Schubert variety is stable under the torus. -/
theorem oppositeSchubertVariety_torus_stable (w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G w)) := by
  let b := (GroupActions.oppositeBorelPointsMulEquiv G).symm
    ⟨GroupActions.torusPointsMulEquiv G t,
      G.torus_le_oppositeBorel (GroupActions.torusPointsMulEquiv G t).property⟩
  have he : t • x = b • x := by
    obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
    rw [torusFlag_smul, oppositeBorelFlag_smul, MulEquiv.apply_symm_apply]
  rw [he]
  exact oppositeSchubertVariety_stable G w b hx

/-- Rational points of a Richardson variety are the intersection of the two Schubert images. -/
theorem richardson_points_range (v w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G v w)) =
      Set.range (GroupActions.Variety.mapPoints (schubertInclusion G w)) ∩
        Set.range (GroupActions.Variety.mapPoints (oppositeSchubertInclusion G v)) := by
  rw [GroupActions.Variety.range_mapPoints, richardsonInclusion_range, Set.preimage_inter,
    ← GroupActions.Variety.range_mapPoints, ← GroupActions.Variety.range_mapPoints]

/-- Rational points of an open Richardson stratum are the intersection of the two cell images. -/
theorem richardsonCell_points_range (v w : G.weylGroup) :
    Set.range (GroupActions.Variety.mapPoints (richardsonCellInclusion G v w)) =
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) ∩
        Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)) := by
  rw [GroupActions.Variety.range_mapPoints, richardsonCellInclusion_range, Set.preimage_inter,
    ← GroupActions.Variety.range_mapPoints, ← GroupActions.Variety.range_mapPoints]

/-- The rational image of a Richardson variety is stable under the torus. -/
theorem richardsonVariety_torus_stable (v w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G v w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G v w)) := by
  rw [richardson_points_range] at hx ⊢
  exact ⟨schubertVariety_torus_stable G w t hx.1,
    oppositeSchubertVariety_torus_stable G v t hx.2⟩

/-- The rational image of an open Richardson stratum is stable under the torus. -/
theorem richardsonCell_torus_stable (v w : G.weylGroup)
    (t : (GroupActions.torusVariety G).points) {x : (flagVariety G).points}
    (hx : x ∈ Set.range (GroupActions.Variety.mapPoints (richardsonCellInclusion G v w))) :
    t • x ∈ Set.range (GroupActions.Variety.mapPoints (richardsonCellInclusion G v w)) := by
  rw [richardsonCell_points_range] at hx ⊢
  exact ⟨schubertCell_torus_stable G w t hx.1, oppositeSchubertCell_torus_stable G v t hx.2⟩

end
end SchubertGeometry
