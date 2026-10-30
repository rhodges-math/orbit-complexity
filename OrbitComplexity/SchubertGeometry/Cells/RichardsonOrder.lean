import OrbitComplexity.SchubertGeometry.Deodhar.ComponentCover
import OrbitComplexity.BruhatIntervals.Words.Subword
import OrbitComplexity.SchubertGeometry.Parabolics.Order
import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.SchubertGeometry.Cells.ActionPoints
import Batteries.Tactic.Lint

/-! # Bruhat comparison from a nonempty Richardson stratum

The Deodhar cover supplies a subexpression ending at the opposite-cell label.
Its selected subword places that label below the ordinary-cell label.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups BruhatIntervals
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- An open Richardson stratum with a scheme point has Bruhat-comparable indices. -/
theorem richardsonCell_order (a b : G.weylGroup)
    (x : (richardsonCell G a b).scheme) : WeylBruhatLE G.rootBase a b := by
  obtain ⟨word, hred, hword⟩ := (weylCoxeterSystem G.rootBase).exists_isReduced b
  rw [weylCoxeterSystem_wordProd] at hword
  subst b
  have hx : (richardsonCellInclusion G a (simpleWeylWord G.rootBase word)).left x ∈
      Set.range (richardsonCellInclusion G a (simpleWeylWord G.rootBase word)).left := ⟨x, rfl⟩
  rw [← deodharRichardson_cover G word hred a] at hx
  obtain ⟨e, _⟩ := Set.mem_iUnion.mp hx
  have hle := (weylCoxeterSystem G.rootBase).bruhatLE_wordProd_of_sublist hred
    e.val.selectedWord_sublist
  rw [e.val.wordProd_selectedWord, e.property.2, weylCoxeterSystem_wordProd] at hle
  exact (weyl_bruhat_iff G.rootBase a (simpleWeylWord G.rootBase word)).mpr hle

private theorem weylFlag_mem_opposite_iff (a z : G.weylGroup) :
    weylFlagPoint G z ∈ Set.range (GroupActions.Variety.mapPoints
      (X := oppositeSchubertVariety G a) (Y := flagVariety G)
      (oppositeSchubertInclusion G a)) ↔ WeylBruhatLE G.rootBase a z := by
  rw [oppositeSchubert_points_cells]
  constructor
  · intro hz
    obtain ⟨v, hav, hcell⟩ := Set.mem_iUnion₂.mp hz
    rw [oppositeSchubertCell_points_range] at hcell
    have hvz := oppositeSchubertOrbits_disjoint G hcell (MulAction.mem_orbit_self _)
    simpa only [hvz] using hav
  · intro haz
    refine Set.mem_iUnion₂.mpr ⟨z, haz, ?_⟩
    rw [oppositeSchubertCell_points_range]
    exact MulAction.mem_orbit_self _

/-- A Weyl flag belongs to the Richardson variety exactly for a Bruhat interval label. -/
theorem weylFlag_mem_richardson_iff (a b z : G.weylGroup) :
    weylFlagPoint G z ∈
      Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G a b)) ↔
        WeylBruhatLE G.rootBase a z ∧ WeylBruhatLE G.rootBase z b := by
  rw [richardson_points_range, Set.mem_inter_iff, weylFlag_mem_schubert_iff,
    weylFlag_mem_opposite_iff]
  exact and_comm

/-- The fixed Richardson points are precisely the Weyl flags in its Bruhat interval. -/
theorem richardson_torus_fixed_iff (a b : G.weylGroup)
    (x : (richardsonVariety G a b).points) :
    (∀ t : (GroupActions.torusVariety G).points, t • x = x) ↔
      ∃ z : G.weylGroup, WeylBruhatLE G.rootBase a z ∧ WeylBruhatLE G.rootBase z b ∧
        GroupActions.Variety.mapPoints (richardsonInclusion G a b) x = weylFlagPoint G z := by
  constructor
  · intro hx
    have hflag (t : (GroupActions.torusVariety G).points) :
        t • GroupActions.Variety.mapPoints (richardsonInclusion G a b) x =
          GroupActions.Variety.mapPoints (richardsonInclusion G a b) x := by
      rw [← richardson_torus_smul, hx t]
    obtain ⟨z, hz⟩ := (torus_fixed_iff_weylFlag G _).mp hflag
    have hbounds := (weylFlag_mem_richardson_iff G a b z).mp ⟨x, hz⟩
    exact ⟨z, hbounds.1, hbounds.2, hz⟩
  · rintro ⟨z, _haz, _hzb, hz⟩
    intro t
    apply GroupActions.Variety.mapPoints_injective_of_mono (richardsonInclusion G a b)
    rw [richardson_torus_smul, hz]
    exact (torus_fixed_iff_weylFlag G (weylFlagPoint G z)).mpr ⟨z, rfl⟩ t

end
end SchubertGeometry
