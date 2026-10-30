import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition
import OrbitComplexity.SchubertGeometry.Cells.RootFactors

/-! # Opposite-unipotent frames of rational flags

Opposite Borel points factor into opposite-unipotent and torus points. The torus factor
can be absorbed into the right Borel coset of a Weyl representative.
-/

open ReductiveGroups TauCeti
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- An opposite Borel point is the product of an opposite-unipotent point and a torus point. -/
theorem oppositeBorelFactorization (b : G.points) (hb : b ∈ G.oppositeBorelPoints) :
    ∃ u ∈ G.oppositeUnipotentPoints, ∃ t ∈ G.torusPoints, u * t = b := by
  let c := G.longestPoint⁻¹ * b * G.longestPoint
  have hc : c ∈ G.borelPoints := by
    apply (G.conj_mem_oppositeBorel c).mp
    have he : G.longestPoint * c * G.longestPoint⁻¹ = b := by dsimp only [c]; group
    rwa [he]
  obtain ⟨t, ht, u, hu, he⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive c⁻¹ (G.borelPoints.inv_mem hc)
  have hfactor : u⁻¹ * t⁻¹ = c := by
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he
  let u' := G.longestPoint * u⁻¹ * G.longestPoint⁻¹
  let t' := G.longestPoint * t⁻¹ * G.longestPoint⁻¹
  have hu' : u' ∈ G.oppositeUnipotentPoints :=
    (G.conj_mem_oppositeUnipotent u⁻¹).mpr (G.unipotentPoints.inv_mem hu)
  have ht' : t' ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff.mp G.longestPoint_mem_normalizer t⁻¹).mp
      (G.torusPoints.inv_mem ht)
  refine ⟨u', hu', t', ht', ?_⟩
  calc
    u' * t' = G.longestPoint * (u⁻¹ * t⁻¹) * G.longestPoint⁻¹ := by
      dsimp only [u', t']
      group
    _ = G.longestPoint * c * G.longestPoint⁻¹ := by rw [hfactor]
    _ = b := by dsimp only [c]; group

/-- Every rational point of an opposite cell has an opposite-unipotent Weyl frame. -/
theorem oppositeCell_unipotent_form (v : G.weylGroup) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v))) :
    ∃ u ∈ G.oppositeUnipotentPoints,
      q = flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v)) := by
  rw [oppositeSchubertCell_points_range] at hq
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hq
  let bm : G.points := GroupActions.oppositeBorelPointsMulEquiv G b
  obtain ⟨u, hu, t, ht, he⟩ := oppositeBorelFactorization G bm
    (GroupActions.oppositeBorelPointsMulEquiv G b).property
  refine ⟨u, hu, ?_⟩
  rw [← hb, weylFlagPoint, oppositeBorelFlag_smul]
  change flagVarietyPointsEquiv G (flagProjection G (bm * G.weylPoint v)) = _
  rw [← he]
  apply congrArg (flagVarietyPointsEquiv G)
  apply (flagProjection_eq_iff G _ _).mpr
  have htor := (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer v) t).mp ht
  have hinv := G.torus_le_borel (G.torusPoints.inv_mem htor)
  convert hinv using 1
  group

end SchubertGeometry
