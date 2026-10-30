import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.SchubertGeometry.Cells.RichardsonOrder

/-! # Richardson strata in closed Richardson varieties

The two Schubert decompositions label every scheme point. Closure order and the
nonempty stratum criterion place both labels in the prescribed Bruhat interval.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem richardson_cover (x : (flagVariety G).scheme) :
    ∃ a b : G.weylGroup, x ∈ Set.range (richardsonCellInclusion G a b).left := by
  obtain ⟨b, hb⟩ := schubertCells_cover G x
  obtain ⟨a, ha⟩ := oppositeSchubertCells_cover G x
  exact ⟨a, b, (richardsonCellInclusion_range G a b).symm ▸ ⟨hb, ha⟩⟩

omit [CharZero K] in
private theorem range_inter_points {X A B : Variety K}
    (f : A.toOver ⟶ X.toOver) (g : B.toOver ⟶ X.toOver)
    (hne : (Set.range f.left ∩ Set.range g.left).Nonempty) :
    ∃ x : X.points, x ∈ Set.range (Variety.mapPoints f) ∧
      x ∈ Set.range (Variety.mapPoints g) := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  obtain ⟨p, hp, hpc⟩ := constructible_closedPoint (X := X.scheme)
    ((Variety.isConstructible_range f).inter (Variety.isConstructible_range g)) hne
  obtain ⟨x, hx⟩ := X.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
  have hpx : X.pointMap x = p := congrArg Subtype.val hx
  refine ⟨x, Variety.exists_mapPoints_eq f x ?_, Variety.exists_mapPoints_eq g x ?_⟩
  · simpa only [hpx] using hp.1
  · simpa only [hpx] using hp.2

private theorem ordinary_order (b v : G.weylGroup) (p : (flagVariety G).scheme)
    (hc : p ∈ Set.range (schubertCellInclusion G b).left)
    (hv : p ∈ Set.range (schubertInclusion G v).left) :
    WeylBruhatLE G.rootBase b v := by
  obtain ⟨x, hxb, hxv⟩ := range_inter_points
    (schubertCellInclusion G b) (schubertInclusion G v) ⟨p, hc, hv⟩
  rw [schubertVariety_points_cells] at hxv
  obtain ⟨c, hcv, hxc⟩ := Set.mem_iUnion₂.mp hxv
  rw [schubertCell_points_range] at hxb hxc
  have hbc := schubertOrbits_disjoint G hxb hxc
  simpa only [hbc] using hcv

private theorem opposite_order (u a : G.weylGroup) (p : (flagVariety G).scheme)
    (hc : p ∈ Set.range (oppositeSchubertCellInclusion G a).left)
    (hu : p ∈ Set.range (oppositeSchubertInclusion G u).left) :
    WeylBruhatLE G.rootBase u a := by
  obtain ⟨x, hxa, hxu⟩ := range_inter_points
    (oppositeSchubertCellInclusion G a) (oppositeSchubertInclusion G u) ⟨p, hc, hu⟩
  rw [oppositeSchubert_points_cells] at hxu
  obtain ⟨c, huc, hxc⟩ := Set.mem_iUnion₂.mp hxu
  rw [oppositeSchubertCell_points_range] at hxa hxc
  have hac := oppositeSchubertOrbits_disjoint G hxa hxc
  simpa only [hac] using huc

private theorem ordinary_subset (b v : G.weylGroup) (hbv : WeylBruhatLE G.rootBase b v) :
    Set.range (schubertCellInclusion G b).left ⊆ Set.range (schubertInclusion G v).left := by
  apply Variety.range_subset_of_mapPoints
  intro x hx
  rw [schubertVariety_points_cells]
  exact Set.mem_iUnion₂.mpr ⟨b, hbv, hx⟩

private theorem opposite_subset (u a : G.weylGroup) (hua : WeylBruhatLE G.rootBase u a) :
    Set.range (oppositeSchubertCellInclusion G a).left ⊆
      Set.range (oppositeSchubertInclusion G u).left := by
  apply Variety.range_subset_of_mapPoints
  intro x hx
  rw [oppositeSchubert_points_cells]
  exact Set.mem_iUnion₂.mpr ⟨a, hua, hx⟩

/-- Each scheme point of a Richardson variety lies in a stratum of its Bruhat interval. -/
theorem richardsonVariety_cells_cover (u v : G.weylGroup)
    (x : (richardsonVariety G u v).scheme) :
    ∃ a b : G.weylGroup, WeylBruhatLE G.rootBase u a ∧
      WeylBruhatLE G.rootBase a b ∧ WeylBruhatLE G.rootBase b v ∧
        (richardsonInclusion G u v).left x ∈
          Set.range (richardsonCellInclusion G a b).left := by
  let p := (richardsonInclusion G u v).left x
  have hp : p ∈ Set.range (richardsonInclusion G u v).left := ⟨x, rfl⟩
  rw [richardsonInclusion_range] at hp
  obtain ⟨a, b, hab⟩ := richardson_cover G p
  obtain ⟨y, hy⟩ := hab
  have hc : p ∈ Set.range (richardsonCellInclusion G a b).left := ⟨y, hy⟩
  rw [richardsonCellInclusion_range] at hc
  exact ⟨a, b, opposite_order G u a p hc.2 hp.2,
    richardsonCell_order G a b y, ordinary_order G b v p hc.1 hp.1, ⟨y, hy⟩⟩

/-- A Richardson variety is the union of the open strata in its Bruhat interval. -/
theorem richardsonVariety_cells_range (u v : G.weylGroup) :
    Set.range (richardsonInclusion G u v).left =
      ⋃ a : G.weylGroup, ⋃ b : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase u a),
        ⋃ (_ : WeylBruhatLE G.rootBase a b), ⋃ (_ : WeylBruhatLE G.rootBase b v),
          Set.range (richardsonCellInclusion G a b).left := by
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, b, hua, hab, hbv, hx⟩ := richardsonVariety_cells_cover G u v x
    exact ⟨a, b, hua, hab, hbv, hx⟩
  · rintro ⟨a, b, hua, _, hbv, hp⟩
    rw [richardsonCellInclusion_range] at hp
    rw [richardsonInclusion_range]
    exact ⟨ordinary_subset G b v hbv hp.1, opposite_subset G u a hua hp.2⟩

end
end SchubertGeometry
