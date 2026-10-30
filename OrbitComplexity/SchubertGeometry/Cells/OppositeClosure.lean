import OrbitComplexity.ReductiveGroups.Roots.Coxeter.LongestOrder
import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition
import OrbitComplexity.SchubertGeometry.Parabolics.BruhatClosure
import OrbitComplexity.SchubertGeometry.Parabolics.Order

/-! # The upper cells of opposite Schubert varieties

Longest translation carries opposite Borel orbits to ordinary Borel orbits.
The resulting homeomorphism transports orbit closures and reverses their Bruhat indices.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def longestTranslation : (flagVariety G).points ≃ₜ (flagVariety G).points :=
  (flagVarietyPointsHomeomorph G).symm.trans
    ((flagTranslation G G.longestPoint⁻¹).trans (flagVarietyPointsHomeomorph G))

attribute [local irreducible] longestTranslation

private theorem translation_flag (g : G.points) :
    longestTranslation G (flagVarietyPointsEquiv G (flagProjection G g)) =
      flagVarietyPointsEquiv G (flagProjection G (G.longestPoint⁻¹ * g)) := by
  unfold longestTranslation
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [show (flagVarietyPointsHomeomorph G).symm
      (flagVarietyPointsEquiv G (flagProjection G g)) = flagProjection G g from
    (flagVarietyPointsHomeomorph G).symm_apply_apply (flagProjection G g)]
  change flagVarietyPointsEquiv G (G.longestPoint⁻¹ • flagProjection G g) = _
  rw [← flagProjection_smul]

private theorem opposite_orbit_translate (w : G.weylGroup)
    (x : (flagVariety G).points) :
    x ∈ MulAction.orbit (oppositeBorelVariety G).points (weylFlagPoint G w) ↔
      longestTranslation G x ∈ MulAction.orbit (borelVariety G).points
        (weylFlagPoint G (G.longestElement⁻¹ * w)) := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  rw [translation_flag]
  exact (mem_oppositeOrbit_iff G w g).trans
    (mem_schubertOrbit_iff G (G.longestElement⁻¹ * w) (G.longestPoint⁻¹ * g)).symm

private theorem opposite_cell_preimage (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := oppositeSchubertCell G w)
      (Y := flagVariety G) (oppositeSchubertCellInclusion G w)) =
      (longestTranslation G) ⁻¹' Set.range (Variety.mapPoints
        (X := schubertCell G (G.longestElement⁻¹ * w)) (Y := flagVariety G)
        (schubertCellInclusion G (G.longestElement⁻¹ * w))) := by
  apply Set.ext
  intro x
  exact (Set.ext_iff.mp (oppositeSchubertCell_points_range G w) x).trans
    ((opposite_orbit_translate G w x).trans
      (Set.ext_iff.mp (schubertCell_points_range G (G.longestElement⁻¹ * w))
        (longestTranslation G x)).symm)

private theorem opposite_closure_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := oppositeSchubertVariety G w)
      (Y := flagVariety G) (oppositeSchubertInclusion G w)) =
      closure (Set.range (Variety.mapPoints (X := oppositeSchubertCell G w)
      (Y := flagVariety G) (oppositeSchubertCellInclusion G w))) := by
  rw [(flagVariety G).isEmbedding_pointMap.closure_eq_preimage_closure_image]
  change _ = (flagVariety G).pointMap ⁻¹' (flagVariety G).pointClosure _
  rw [(oppositeSchubertCell G w).pointClosure_range, Variety.range_mapPoints,
    oppositeSchubertInclusion_range]

private theorem ordinary_closure_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := schubertVariety G w)
      (Y := flagVariety G) (schubertInclusion G w)) =
      closure (Set.range (Variety.mapPoints (X := schubertCell G w)
      (Y := flagVariety G) (schubertCellInclusion G w))) := by
  rw [(flagVariety G).isEmbedding_pointMap.closure_eq_preimage_closure_image]
  change _ = (flagVariety G).pointMap ⁻¹' (flagVariety G).pointClosure _
  rw [(schubertCell G w).pointClosure_range, Variety.range_mapPoints, schubertInclusion_range]

private theorem opposite_order_iff (a b : G.weylGroup) :
    WeylBruhatLE G.rootBase (G.longestElement⁻¹ * a) (G.longestElement⁻¹ * b) ↔
      WeylBruhatLE G.rootBase b a := by
  have hi : G.longestElement⁻¹ = G.longestElement := by
    apply mul_left_cancel (a := G.longestElement)
    rw [mul_inv_cancel]
    exact (longestWeylElement_sq G.rootBase).symm
  rw [hi, weyl_bruhat_iff, weyl_bruhat_iff]
  exact bruhat_longest_mul_iff G.rootBase a b

/-- Opposite Schubert rational points are the opposite cells above their Weyl element. -/
theorem oppositeSchubert_points_cells (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := oppositeSchubertVariety G w)
      (Y := flagVariety G) (oppositeSchubertInclusion G w)) =
      ⋃ v : G.weylGroup, ⋃ (_ : WeylBruhatLE G.rootBase w v),
        Set.range (Variety.mapPoints (X := oppositeSchubertCell G v)
      (Y := flagVariety G) (oppositeSchubertCellInclusion G v)) := by
  rw [opposite_closure_points, opposite_cell_preimage, ← Homeomorph.preimage_closure,
    ← ordinary_closure_points, schubertVariety_points_cells]
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
    let v := G.longestElement * a
    have hv : G.longestElement⁻¹ * v = a := by dsimp only [v]; group
    have horder : WeylBruhatLE G.rootBase w v :=
      (opposite_order_iff G v w).mp (hv ▸ ha)
    refine Set.mem_iUnion₂.mpr ⟨v, horder, ?_⟩
    rw [opposite_cell_preimage, Set.mem_preimage, hv]
    exact hxa
  · intro hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [opposite_cell_preimage, Set.mem_preimage] at hxv
    exact Set.mem_iUnion₂.mpr ⟨G.longestElement⁻¹ * v,
      (opposite_order_iff G v w).mpr hv, hxv⟩

end
end SchubertGeometry
