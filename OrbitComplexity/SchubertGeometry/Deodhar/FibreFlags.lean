import OrbitComplexity.SchubertGeometry.Deodhar.StepFlags
import OrbitComplexity.SchubertGeometry.Deodhar.NegativeProducts
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints
import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition


/-! # Opposite-cell conditions in a rank-one fibre

The additive cell chart has two opposite-cell strata at an ascent: zero and nonzero.
At a descent its entire additive fibre lies in the reflected opposite cell.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

open BruhatIntervals ReductiveGroups SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem map_mem_of_eq {A B : Type*} (f : A → B) (S : Set B)
    {a b : A} (h : a = b) (hb : f b ∈ S) : f a ∈ S := h.symm ▸ hb

private theorem zero_product {H : Type*} [Group H] (g n u x r : H)
    (hg : g = u * n) (hx : x = 1) : g * x * r = u * (n * r) := by
  rw [hg, hx, mul_one, mul_assoc]

private theorem cancel_frame {H : Type*} [Group H] (u n y : H) :
    (u * (n * y * n⁻¹)) * n = (u * n) * y := by group

private theorem extend_frame {H : Type*} [Group H] (u n x r : H) :
    u * n * x * r = (u * (n * x * n⁻¹)) * (n * r) := by group

private theorem normalizer_extend_flag (n : G.points) (v : G.weylGroup)
    (hn : n ∈ G.torusNormalizer)
    (hf : flagProjection G n = flagProjection G (G.weylPoint v))
    (i : G.rootBase.support) :
    flagProjection G (n * (G.reflectionPoint i.val)⁻¹) =
      flagProjection G (G.weylPoint (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  have ht : n⁻¹ * G.weylPoint v ∈ G.torusPoints := by
    have h : n⁻¹ * G.weylPoint v ∈ G.borelPoints ⊓ G.torusNormalizer :=
      ⟨(flagProjection_eq_iff G _ _).mp hf,
        G.torusNormalizer.mul_mem (G.torusNormalizer.inv_mem hn)
          (G.weylPoint_mem_normalizer v)⟩
    rwa [G.borel_inf_torus_normalizer] at h
  have he : flagProjection G (n * (G.reflectionPoint i.val)⁻¹) =
      flagProjection G (G.weylPoint v * (G.reflectionPoint i.val)⁻¹) := by
    apply (flagProjection_eq_iff G _ _).mpr
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (G.isBruhatSystem.weyl.mem_normalizer i.val) (n⁻¹ * G.weylPoint v)).mp ht
    have hmul : (n * (G.reflectionPoint i.val)⁻¹)⁻¹ *
        (G.weylPoint v * (G.reflectionPoint i.val)⁻¹) =
        G.reflectionPoint i.val * (n⁻¹ * G.weylPoint v) * (G.reflectionPoint i.val)⁻¹ := by
      group
    rw [hmul]
    exact G.torus_le_borel hmem
  exact he.trans (inverseSimple_flag G v i)

private theorem opposite_of_factor (u n : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
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

/-- The zero additive coordinate has the reflected opposite-cell index. -/
theorem prefixFibre_zero
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (k : ℕ) (i : G.rootBase.support) :
    flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) (0 : K) * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) k *
          RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  obtain ⟨u, hu, hp⟩ := deodharPrefix_mem_opposite G expression hd parameters k
  let n := subwordRepresentative G expression k
  let v := expression.prefixProd (weylCoxeterSystem G.rootBase) k
  let r := (G.reflectionPoint i.val)⁻¹
  have hf : flagProjection G (n * r) = flagProjection G
      (G.weylPoint (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
    normalizer_extend_flag G n v (subwordRepresentative_mem_normalizer G expression k)
      (subwordRepresentative_flag G expression k) i
  have hm := opposite_of_factor G u (n * r) hu
    (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val) hf
  have hz : gaParameterPoint (G.simpleRootMap i) (0 : K) = 1 :=
    gaParameterPoint_zero (G.simpleRootMap i)
  exact map_mem_of_eq (fun g : G.points => flagVarietyPointsEquiv G (flagProjection G g))
    (Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))))
    (zero_product (deodharPrefix G expression parameters k) n u
      (gaParameterPoint (G.simpleRootMap i) (0 : K)) r hp hz) hm

/-- A nonzero coordinate at an ascent retains the preceding opposite-cell index. -/
theorem prefixFibre_ascent
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (k : ℕ) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i.val))
    (t : K) (ht : t ≠ 0) :
    flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) k))) := by
  obtain ⟨u, hu, hp⟩ := deodharPrefix_mem_opposite G expression hd parameters k
  let n := subwordRepresentative G expression k
  let a := n * gaParameterPoint (G.negativeSimpleRootMap i) t⁻¹ * n⁻¹
  have ha : a ∈ G.oppositeUnipotentPoints :=
    negativeSimple_conj_opposite G n
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k)
      (subwordRepresentative_transport G expression k) i hi t⁻¹
  have he : flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹) =
      flagProjection G ((u * a) * n) := by
    rw [hp]
    have hf := congrArg (fun q : flagPoints G => (u * n) • q)
      (simpleRoot_flag_eq_negative G i ht)
    change flagProjection G ((u * n) * (gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹)) =
      flagProjection G ((u * n) * gaParameterPoint (G.negativeSimpleRootMap i) t⁻¹) at hf
    change flagProjection G _ = flagProjection G ((u * (n *
      gaParameterPoint (G.negativeSimpleRootMap i) t⁻¹ * n⁻¹)) * n)
    rw [cancel_frame]
    simpa only [mul_assoc, n] using hf
  rw [he]
  exact opposite_of_factor G (u * a) n (G.oppositeUnipotentPoints.mul_mem hu ha)
    (expression.prefixProd (weylCoxeterSystem G.rootBase) k)
    (subwordRepresentative_flag G expression k)

/-- Every coordinate at a descent has the reflected opposite-cell index. -/
theorem prefixFibre_descent
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (k : ℕ) (i : G.rootBase.support)
    (hi : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) k *
          RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  obtain ⟨u, hu, hp⟩ := deodharPrefix_mem_opposite G expression hd parameters k
  let n := subwordRepresentative G expression k
  let a := n * gaParameterPoint (G.simpleRootMap i) t * n⁻¹
  have ha : a ∈ G.oppositeUnipotentPoints :=
    positiveSimple_conj_opposite G n
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k)
      (subwordRepresentative_transport G expression k) i hi t
  have he : deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹ =
      (u * a) * (n * (G.reflectionPoint i.val)⁻¹) := by
    rw [hp]
    exact extend_frame u n _ _
  have hm := opposite_of_factor G (u * a) (n * (G.reflectionPoint i.val)⁻¹)
    (G.oppositeUnipotentPoints.mul_mem hu ha)
    (expression.prefixProd (weylCoxeterSystem G.rootBase) k *
      RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    (normalizer_extend_flag G n (expression.prefixProd (weylCoxeterSystem G.rootBase) k)
      (subwordRepresentative_mem_normalizer G expression k)
      (subwordRepresentative_flag G expression k) i)
  exact map_mem_of_eq (fun g : G.points => flagVarietyPointsEquiv G (flagProjection G g))
    (Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k *
        RootPairing.weylGroup.ofIdx G.rootSystem i.val)))) he hm

private theorem mul_simple_ne {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (v : W) (i : B) : v * cs.simple i ≠ v := by
  intro h
  have hi : cs.simple i = 1 := mul_left_cancel (h.trans (mul_one v).symm)
  have hlen := cs.length_simple i
  rw [hi, cs.length_one] at hlen
  omega

private theorem opposite_index_eq {v w : G.weylGroup} {x : (flagVariety G).points}
    (hv : x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G v)))
    (hw : x ∈ Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G w))) :
    v = w := by
  rw [oppositeSchubertCell_points_range] at hv hw
  exact oppositeSchubertOrbits_disjoint G hv hw

/-- At an ascent, the reflected opposite cell is exactly the zero-coordinate locus. -/
theorem prefixFibre_ascent_zero_iff
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (k : ℕ) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) k *
          RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have he := opposite_index_eq G (prefixFibre_ascent G expression hd parameters k i hi t ht) h
    have hn := mul_simple_ne (weylCoxeterSystem G.rootBase)
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i
    exact hn (by simpa only [weylCoxeterSystem_simple] using he.symm)
  · rintro rfl
    exact prefixFibre_zero G expression hd parameters k i

/-- At an ascent, the preceding opposite cell is exactly the nonzero-coordinate locus. -/
theorem prefixFibre_ascent_nonzero_iff
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (k : ℕ) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i.val)) (t : K) :
    flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression parameters k *
      gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) ∈
      Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
        (expression.prefixProd (weylCoxeterSystem G.rootBase) k))) ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    have he := opposite_index_eq G (prefixFibre_zero G expression hd parameters k i) h
    have hn := mul_simple_ne (weylCoxeterSystem G.rootBase)
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k) i
    exact hn (by simpa only [weylCoxeterSystem_simple] using he)
  · exact prefixFibre_ascent G expression hd parameters k i hi t

end
end SchubertGeometry
