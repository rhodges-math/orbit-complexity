import OrbitComplexity.SchubertGeometry.Cells.OppositeFrames
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints
import OrbitComplexity.SchubertGeometry.Deodhar.RepresentativeFlags
import OrbitComplexity.SchubertGeometry.Deodhar.RankOnePoints

/-! # Opposite cells in a simple-root fibre

For an opposite-unipotent Weyl frame, simple-root parameters have zero and nonzero
opposite-cell strata at an ascent, and one reflected stratum at a descent.
-/

open ReductiveGroups TauCeti
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem opposite_of_frame (u n : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (hf : flagProjection G n = flagProjection G (G.weylPoint v)) :
    flagVarietyPointsEquiv G (flagProjection G (u * n)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)) := by
  rw [oppositeSchubertCell_points_range]
  let b : (GroupActions.oppositeBorelVariety G).points :=
    (GroupActions.oppositeBorelPointsMulEquiv G).symm
      ⟨u, G.oppositeUnipotent_le_oppositeBorel hu⟩
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨b, ?_⟩
  rw [weylFlagPoint, oppositeBorelFlag_smul]
  have hb : (GroupActions.oppositeBorelPointsMulEquiv G b : G.points) = u :=
    congrArg Subtype.val ((GroupActions.oppositeBorelPointsMulEquiv G).apply_symm_apply _)
  rw [hb]
  apply congrArg (flagVarietyPointsEquiv G)
  change u • flagProjection G (G.weylPoint v) = u • flagProjection G n
  exact congrArg (fun q : flagPoints G => u • q) hf.symm

set_option maxHeartbeats 400000 in
/-- The zero coordinate in an opposite-unipotent frame has the reflected cell index. -/
theorem oppositeFibre_zero (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) (0 : K) * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  rw [gaParameterPoint_zero, mul_one, mul_assoc]
  exact opposite_of_frame G u (G.weylPoint v * (G.reflectionPoint i.val)⁻¹) hu
    (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val) (inverseSimple_flag G v i)

/-- At an ascent, a nonzero fibre coordinate retains the opposite-cell index of its frame. -/
theorem oppositeFibre_ascent (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val))
    (t : K) (ht : t ≠ 0) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)) := by
  let n := G.weylPoint v
  let a := n * gaParameterPoint (G.negativeSimpleRootMap i) t⁻¹ * n⁻¹
  have ha : a ∈ G.oppositeUnipotentPoints :=
    negativeSimple_conj_opposite G n v (G.weylPoint_rootWeightSpace v) i hi t⁻¹
  have he : flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹) =
        flagProjection G ((u * a) * n) := by
    have hf := congrArg (fun q : flagPoints G => (u * n) • q)
      (simpleRoot_flag_eq_negative G i ht)
    change flagProjection G ((u * n) * (gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹)) =
        flagProjection G ((u * n) * gaParameterPoint (G.negativeSimpleRootMap i) t⁻¹) at hf
    calc
      _ = flagProjection G ((u * n) * (gaParameterPoint (G.simpleRootMap i) t *
          (G.reflectionPoint i.val)⁻¹)) := by simp only [n, mul_assoc]
      _ = _ := hf
      _ = flagProjection G ((u * a) * n) := by
        apply congrArg (flagProjection G)
        dsimp only [a]
        group
  rw [he]
  exact opposite_of_frame G (u * a) n (G.oppositeUnipotentPoints.mul_mem hu ha) v rfl

/-- At a descent, every fibre coordinate has the reflected opposite-cell index. -/
theorem oppositeFibre_descent (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support)
    (hi : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  let n := G.weylPoint v
  let a := n * gaParameterPoint (G.simpleRootMap i) t * n⁻¹
  have ha : a ∈ G.oppositeUnipotentPoints :=
    positiveSimple_conj_opposite G n v (G.weylPoint_rootWeightSpace v) i hi t
  have he : u * G.weylPoint v * gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹ =
        (u * a) * (n * (G.reflectionPoint i.val)⁻¹) := by dsimp only [a, n]; group
  rw [he]
  exact opposite_of_frame G (u * a) (n * (G.reflectionPoint i.val)⁻¹)
    (G.oppositeUnipotentPoints.mul_mem hu ha)
    (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val) (inverseSimple_flag G v i)

private theorem reflected_ne (v : G.weylGroup) (i : G.rootBase.support) :
    v * RootPairing.weylGroup.ofIdx G.rootSystem i.val ≠ v := by
  intro h
  have hs : (weylCoxeterSystem G.rootBase).simple i = 1 :=
    mul_left_cancel (h.trans (mul_one v).symm)
  have hlen := (weylCoxeterSystem G.rootBase).length_simple i
  rw [hs, (weylCoxeterSystem G.rootBase).length_one] at hlen
  omega

private theorem opposite_index_eq {v w : G.weylGroup} {q : (flagVariety G).points}
    (hv : q ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)))
    (hw : q ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w))) :
    v = w := by
  rw [oppositeSchubertCell_points_range] at hv hw
  exact oppositeSchubertOrbits_disjoint G hv hw

/-- At an ascent, the reflected opposite cell is exactly the zero-coordinate fibre locus. -/
theorem oppositeFibre_ascent_zero_iff (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact reflected_ne G v i
      (opposite_index_eq G (oppositeFibre_ascent G u hu v i hi t ht) h).symm
  · rintro rfl
    exact oppositeFibre_zero G u hu v i

/-- At an ascent, the preceding opposite cell is exactly the nonzero-coordinate fibre locus. -/
theorem oppositeFibre_ascent_nonzero_iff (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)) ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    exact reflected_ne G v i (opposite_index_eq G (oppositeFibre_zero G u hu v i) h)
  · exact oppositeFibre_ascent G u hu v i hi t

end SchubertGeometry
