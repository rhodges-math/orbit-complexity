import OrbitComplexity.Paper.Heart.Embedding
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties

/-!
# The ordinary torus action on the heart

Torus normalization of the conjugated root subgroup makes the heart stable in the
flag variety. The induced algebraic action makes its inclusion equivariant.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The I-heart is stable under the ordinary torus action on the flag variety. -/
theorem heart_torus_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) {q : (flagVariety G).points}
    (hq : q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) :
    t • q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  obtain ⟨v, hv, rfl⟩ := (mem_heart_iff G I w q).mp hq
  let g : G.points := torusPointsMulEquiv G t
  let c := g * v * g⁻¹
  have hc : c ∈ Vd.points G I w := by
    rw [Vd.points_eq_rootSubset] at hv ⊢
    exact G.rootSubsetPoints_conjugate_mem _ _ g v
      (torusPointsMulEquiv G t).property hv
  apply (mem_heart_iff G I w _).mpr
  refine ⟨c, hc, ?_⟩
  rw [torusFlag_smul]
  apply congrArg (flagVarietyPointsEquiv G)
  change flagProjection G (c * G.weylPoint w) = flagProjection G (g * (v * G.weylPoint w))
  apply (flagProjection_eq_iff G _ _).mpr
  have ht : (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) g).mp
      (torusPointsMulEquiv G t).property
  convert G.torus_le_borel ht using 1
  dsimp only [c]
  group

/-- The ordinary torus action restricts algebraically to the I-heart. -/
instance heartTorusAction (I : Set G.rootBase.support) (w : G.weylGroup) :
    ModObj (torusVariety G).toOver (heart G I w).toOver :=
  Variety.modObjOfInvariant (torusVariety G) (flagVariety G) (heart G I w)
    (heartInclusion G I w) (fun t h => heart_torus_stable G I w t ⟨h, rfl⟩)

/-- The heart inclusion is equivariant for the ordinary torus actions. -/
instance heartInclusion_isModHom (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (torusVariety G).toOver (heartInclusion G I w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ _

/-- Torus multiplication on the heart agrees with its flag-variety torus action. -/
theorem heart_torus_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) (x : (heart G I w).points) :
    Variety.mapPoints (heartInclusion G I w) (t • x) =
      t • Variety.mapPoints (heartInclusion G I w) x :=
  Variety.modObjOfInvariant_smul _ _ _ _ _ t x

end SchubertOrbits
