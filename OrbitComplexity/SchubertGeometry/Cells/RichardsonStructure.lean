import OrbitComplexity.SchubertGeometry.Cells.RichardsonDimension
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.SchubertGeometry.Cells.Decomposition
import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition

/-! # Richardson varieties and their Bruhat strata

Closure order, integral dimension, the dense open stratum and the disjoint
scheme-point partition describe the geometry of Richardson intersections.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem closure_order (a b : G.weylGroup) :
    Set.range (schubertInclusion G a).left ⊆ Set.range (schubertInclusion G b).left ↔
      (weylCoxeterSystem G.rootBase).BruhatLE a b := by
  constructor
  · intro h
    have hself : weylFlagPoint G a ∈
        Set.range (Variety.mapPoints (schubertCellInclusion G a)) := by
      rw [schubertCell_points_range]
      exact MulAction.mem_orbit_self _
    have hp : (flagVariety G).pointMap (weylFlagPoint G a) ∈
        Set.range (schubertCellInclusion G a).left := by
      change weylFlagPoint G a ∈ (flagVariety G).pointMap ⁻¹'
        Set.range (schubertCellInclusion G a).left
      rwa [← Variety.range_mapPoints]
    have hp' : (flagVariety G).pointMap (weylFlagPoint G a) ∈
        Set.range (schubertInclusion G a).left := by
      rw [schubertInclusion_range]
      exact subset_closure hp
    have hb := h hp'
    change weylFlagPoint G a ∈ (flagVariety G).pointMap ⁻¹'
      Set.range (schubertInclusion G b).left at hb
    rw [← Variety.range_mapPoints, schubertVariety_points_cells] at hb
    obtain ⟨c, hcb, hc⟩ := Set.mem_iUnion₂.mp hb
    rw [schubertCell_points_range] at hself hc
    have he := schubertOrbits_disjoint G hself hc
    exact (weyl_bruhat_iff G.rootBase a b).mp (he.symm ▸ hcb)
  · intro hab
    apply Variety.range_subset_of_mapPoints
    intro x hx
    rw [schubertVariety_points_cells] at hx ⊢
    obtain ⟨c, hca, hc⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨c, hca.trans ((weyl_bruhat_iff G.rootBase a b).mpr hab), hc⟩

private theorem strata_disjoint {a b c d : G.weylGroup} {x : (flagVariety G).scheme}
    (hab : x ∈ Set.range (richardsonCellInclusion G a b).left)
    (hcd : x ∈ Set.range (richardsonCellInclusion G c d).left) : a = c ∧ b = d := by
  rw [richardsonCellInclusion_range] at hab hcd
  exact ⟨oppositeSchubertCells_disjoint G hab.2 hcd.2,
    schubertCells_disjoint G hab.1 hcd.1⟩

/-- Richardson varieties have Bruhat closure order, integral dimension, dense open
strata, disjoint interval strata and compatible torus actions. -/
theorem richardson_structure (a b : G.weylGroup) :
    (Set.range (schubertInclusion G a).left ⊆ Set.range (schubertInclusion G b).left ↔
      (weylCoxeterSystem G.rootBase).BruhatLE a b) ∧
    (Nonempty (richardsonVariety G a b).scheme ↔
      (weylCoxeterSystem G.rootBase).BruhatLE a b) ∧
    ((weylCoxeterSystem G.rootBase).BruhatLE a b →
      IrreducibleSpace (richardsonVariety G a b).scheme ∧
      (richardsonVariety G a b).dim =
        ↑((weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a) ∧
      IsOpenImmersion (richardsonCellToVariety G a b).left ∧
      DenseRange (richardsonCellToVariety G a b).left) ∧
    (Set.range (richardsonInclusion G a b).left =
      ⋃ c : G.weylGroup, ⋃ d : G.weylGroup,
        ⋃ (_ : (weylCoxeterSystem G.rootBase).BruhatLE a c),
        ⋃ (_ : (weylCoxeterSystem G.rootBase).BruhatLE c d),
        ⋃ (_ : (weylCoxeterSystem G.rootBase).BruhatLE d b),
          Set.range (richardsonCellInclusion G c d).left) ∧
    (∀ c d c' d' : G.weylGroup, ∀ x : (flagVariety G).scheme,
      x ∈ Set.range (richardsonCellInclusion G c d).left →
      x ∈ Set.range (richardsonCellInclusion G c' d').left → c = c' ∧ d = d') ∧
    (∀ w : G.weylGroup, ∀ t : (torusVariety G).points, ∀ x : (flagVariety G).points,
      x ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        t • x ∈ Set.range (Variety.mapPoints (schubertInclusion G w))) ∧
    (∀ w : G.weylGroup, ∀ t : (torusVariety G).points, ∀ x : (flagVariety G).points,
      x ∈ Set.range (Variety.mapPoints (oppositeSchubertInclusion G w)) →
        t • x ∈ Set.range (Variety.mapPoints (oppositeSchubertInclusion G w))) ∧
    IsModHom (torusVariety G).toOver (richardsonInclusion G a b) := by
  refine ⟨closure_order G a b, ?_, ?_, ?_, ?_, ?_, ?_, inferInstance⟩
  · simpa only [weyl_bruhat_iff] using richardsonVariety_nonempty_iff G a b
  · intro hab
    let := richardsonVariety_integral G a b ((weyl_bruhat_iff G.rootBase a b).mpr hab)
    exact ⟨inferInstance, richardsonVariety_dim G a b hab, inferInstance,
      (richardsonCellToVariety G a b).left.denseRange⟩
  · simpa only [weyl_bruhat_iff] using richardsonVariety_cells_range G a b
  · intro c d c' d' x hx hy
    exact strata_disjoint G hx hy
  · intro w t x hx
    exact schubertVariety_torus_stable G w t hx
  · intro w t x hx
    exact oppositeSchubertVariety_torus_stable G w t hx

end
end SchubertGeometry
