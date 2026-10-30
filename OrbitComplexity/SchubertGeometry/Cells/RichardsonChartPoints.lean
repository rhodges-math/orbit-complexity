import OrbitComplexity.SchubertGeometry.Cells.RootFactors
import OrbitComplexity.SchubertGeometry.Cells.OppositeActions

/-! # Opposite-unipotent representatives of opposite-cell points

The torus-unipotent factorization of the opposite Borel lets its torus factor act on the right
of a Weyl representative. This gives opposite-unipotent representatives of every cell point.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem opposite_factor (b : G.points) (hb : b ∈ G.oppositeBorelPoints) :
    ∃ m ∈ G.oppositeUnipotentPoints, ∃ z ∈ G.torusPoints, m * z = b := by
  let c := G.longestPoint⁻¹ * b * G.longestPoint
  have hc : c ∈ G.borelPoints := by
    apply (G.conj_mem_oppositeBorel c).mp
    have he : G.longestPoint * c * G.longestPoint⁻¹ = b := by dsimp only [c]; group
    rwa [he]
  obtain ⟨t, ht, u, hu, he⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive c⁻¹ (G.borelPoints.inv_mem hc)
  have hec : u⁻¹ * t⁻¹ = c := by
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he
  let m := G.longestPoint * u⁻¹ * G.longestPoint⁻¹
  let z := G.longestPoint * t⁻¹ * G.longestPoint⁻¹
  have hm : m ∈ G.oppositeUnipotentPoints :=
    (G.conj_mem_oppositeUnipotent u⁻¹).mpr (G.unipotentPoints.inv_mem hu)
  have hz : z ∈ G.torusPoints := by
    have hnorm : G.longestPoint⁻¹ ∈ Subgroup.normalizer (G.torusPoints : Set G.points) :=
      (Subgroup.normalizer _).inv_mem G.longestPoint_mem_normalizer
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff''.mp hnorm t⁻¹).mp (G.torusPoints.inv_mem ht)
  refine ⟨m, hm, z, hz, ?_⟩
  calc
    m * z = G.longestPoint * (u⁻¹ * t⁻¹) * G.longestPoint⁻¹ := by dsimp only [m, z]; group
    _ = G.longestPoint * c * G.longestPoint⁻¹ :=
      congrArg (fun a : G.points => G.longestPoint * a * G.longestPoint⁻¹) hec
    _ = b := by dsimp only [c]; group

/-- Every point of an opposite cell has an opposite-unipotent Weyl representative. -/
theorem oppositeCell_unipotent_points (w : G.weylGroup) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G w))) :
    ∃ m ∈ G.oppositeUnipotentPoints,
      q = flagVarietyPointsEquiv G (flagProjection G (m * G.weylPoint w)) := by
  rw [oppositeSchubertCell_points_range] at hq
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
  rw [weylFlagPoint, oppositeBorelFlag_smul] at hb
  let g : G.points := oppositeBorelPointsMulEquiv G b
  obtain ⟨m, hm, z, hz, hmz⟩ := opposite_factor G g
    (oppositeBorelPointsMulEquiv G b).property
  have ht : (G.weylPoint w)⁻¹ * z⁻¹ * G.weylPoint w ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) z⁻¹).mp
      (G.torusPoints.inv_mem hz)
  have hflag : flagProjection G (g * G.weylPoint w) =
      flagProjection G (m * G.weylPoint w) := by
    rw [← hmz]
    apply (flagProjection_eq_iff G _ _).mpr
    have he : (m * z * G.weylPoint w)⁻¹ * (m * G.weylPoint w) =
        (G.weylPoint w)⁻¹ * z⁻¹ * G.weylPoint w := by group
    rw [he]
    exact G.torus_le_borel ht
  exact ⟨m, hm, hb.symm.trans (congrArg (flagVarietyPointsEquiv G) hflag)⟩

end
end SchubertGeometry
