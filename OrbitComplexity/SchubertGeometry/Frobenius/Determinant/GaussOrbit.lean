import OrbitComplexity.SchubertGeometry.Cells.RichardsonSchubert
import OrbitComplexity.SchubertGeometry.FlagVariety.QuotientCharts
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The identity Gauss chart and the big opposite cell

An opposite Borel point factors as an opposite unipotent point followed by
a torus point. The torus factor disappears in the flag quotient, so the
identity Gauss chart has exactly the image of the opposite cell at one.
-/

set_option autoImplicit false
noncomputable section

universe u

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions TauCeti

namespace SchubertGeometry.DeterminantSection

open private chart_in_opposite_one from
  OrbitComplexity.SchubertGeometry.Cells.RichardsonSchubert
open private flagProjection_borel from
  OrbitComplexity.SchubertGeometry.FlagVariety.QuotientCharts

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

private theorem oppositeBorel_factor (b : G.points) (hb : b ∈ G.oppositeBorelPoints) :
    ∃ u ∈ G.oppositeUnipotentPoints, ∃ t ∈ G.borelPoints, u * t = b := by
  let c : G.points := G.longestPoint⁻¹ * b * G.longestPoint
  have hc : G.longestPoint * c * G.longestPoint⁻¹ = b := by
    dsimp [c]
    group
  have hcB : c ∈ G.borelPoints := (G.conj_mem_oppositeBorel c).mp (by
    rw [hc]
    exact hb)
  obtain ⟨t, ht, u, hu, htu⟩ :=
    BorelPoint.exists_torus_mul_borelRootUnipotent
      G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
      G.torusSplit G.split_surjective G.split_eq_zero G.reductive
      c⁻¹ (G.borelPoints.inv_mem hcB)
  have huc : u⁻¹ * t⁻¹ = c := by
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv htu
  have huG : u ∈ G.unipotentPoints := hu
  have huOpp : G.longestPoint * u⁻¹ * G.longestPoint⁻¹ ∈
      G.oppositeUnipotentPoints :=
    (G.conj_mem_oppositeUnipotent u⁻¹).mpr (G.unipotentPoints.inv_mem huG)
  have htOpp : G.longestPoint * t⁻¹ * G.longestPoint⁻¹ ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff.mp G.longestPoint_mem_normalizer t⁻¹).mp
      (G.torusPoints.inv_mem ht)
  refine ⟨G.longestPoint * u⁻¹ * G.longestPoint⁻¹, huOpp,
    G.longestPoint * t⁻¹ * G.longestPoint⁻¹, G.torus_le_borel htOpp, ?_⟩
  calc
    (G.longestPoint * u⁻¹ * G.longestPoint⁻¹) *
        (G.longestPoint * t⁻¹ * G.longestPoint⁻¹) =
      G.longestPoint * (u⁻¹ * t⁻¹) * G.longestPoint⁻¹ := by group
    _ = G.longestPoint * c * G.longestPoint⁻¹ := by rw [huc]
    _ = b := hc

/-- The identity Gauss chart and the big opposite cell have the same image
in the underlying flag scheme. -/
theorem gauss_oppositeCell_range :
    Set.range (flagChartMorphism G 1).left =
      Set.range (oppositeSchubertCellInclusion G 1).left := by
  apply (chart_in_opposite_one G).antisymm
  apply Variety.range_subset_of_mapPoints
    (A := oppositeSchubertCell G 1) (B := oppositeUnipotentVariety G)
    (C := flagVariety G) (oppositeSchubertCellInclusion G 1) (flagChartMorphism G 1)
  intro x hx
  rw [oppositeSchubertCell_points_range] at hx
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hx
  have hw : G.weylPoint 1 = 1 := by rw [G.weylPoint_eq, weylElementPoint_one]
  rw [weylFlagPoint, oppositeBorelFlag_smul, ← flagProjection_smul, hw, mul_one] at hb
  let b0 : G.points := oppositeBorelPointsMulEquiv G b
  have hb0 : flagVarietyPointsEquiv G (flagProjection G b0) = x := hb
  obtain ⟨u, hu, t, ht, hut⟩ :=
    oppositeBorel_factor G b0 (oppositeBorelPointsMulEquiv G b).property
  let p : (oppositeUnipotentVariety G).points :=
    (oppositeUnipotentPointsMulEquiv G).symm ⟨u, hu⟩
  have hp : (oppositeUnipotentPointsMulEquiv G p : G.points) = u :=
    congrArg Subtype.val ((oppositeUnipotentPointsMulEquiv G).apply_symm_apply ⟨u, hu⟩)
  refine ⟨p, ?_⟩
  rw [flagChartMorphism_points]
  change flagVarietyPointsEquiv G
    (flagProjection G (1 * (oppositeUnipotentPointsMulEquiv G p : G.points))) = x
  rw [one_mul, hp]
  calc
    flagVarietyPointsEquiv G (flagProjection G u) =
        flagVarietyPointsEquiv G (flagProjection G (u * t)) :=
      congrArg (flagVarietyPointsEquiv G) (flagProjection_borel G u ⟨t, ht⟩).symm
    _ = flagVarietyPointsEquiv G (flagProjection G b0) := by rw [hut]
    _ = x := hb0

end SchubertGeometry.DeterminantSection
