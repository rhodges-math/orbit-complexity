import OrbitComplexity.SchubertGeometry.Deodhar.ParameterFrames
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.GroupActions.Varieties.CoordinateInversion
import OrbitComplexity.SchubertGeometry.Deodhar.FibreFlags
import OrbitComplexity.SchubertGeometry.Deodhar.StepRoots

/-! # Opposite-cell conditions on a parameter step -/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private theorem chosen_next {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) {word : List S} (expression : Subexpression word)
    (n : Fin word.length)
    (hne : expression.prefixProd cs n.val ≠ expression.prefixProd cs (n.val + 1)) :
    expression.prefixProd cs (n.val + 1) =
      expression.prefixProd cs n.val * cs.simple word[n.val] := by
  have h := expression.prefixProd_succ cs n
  split at h
  · exact h
  · simp only [mul_one] at h
    exact False.elim (hne h.symm)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem frame_simple_action (g : G.points) (i : G.rootBase.support) (t : K) :
    reductivePointsEquiv G g • mapPoints
      ((simpleCellIso G i).hom ≫ schubertCellInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem i)) (additivePointsEquiv K t) =
      flagVarietyPointsEquiv G (flagProjection G
        (g * gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) := by
  rw [simpleCellIso_points G i t]
  change reductivePointsMulEquiv G g • _ = _
  rw [flagVarietyAction_points G g]
  change flagVarietyPointsEquiv G (flagProjection G
    (g * (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹))) = _
  rw [mul_assoc]

variable (n : Fin word.length)
  (m : (deodharParameters G (expression.take n.val)).toOver ⊗
    (additiveVariety K).toOver ⟶ (wordCell G word (n.val + 1)).toOver)
  (hm : ∀ (Q : Variety K)
    (a : Q.toOver ⟶ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (q : Q.points),
    mapPoints (a ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) q =
      mapPoints (a ≫ fst (deodharParameters G (expression.take n.val)).toOver
        (additiveVariety K).toOver ≫ deodharPrefixLift G (expression.take n.val) n.val) q •
      mapPoints (a ≫ snd (deodharParameters G (expression.take n.val)).toOver
        (additiveVariety K).toOver ≫ (simpleCellIso G (word[n.val]'n.isLt)).hom ≫
        schubertCellInclusion G
          (RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt))) q)

include hm in
private theorem fibre_frame (Q : Variety K)
    (a : Q.toOver ⟶ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (q : Q.points) (p : Fin word.length → K) (t : K)
    (hb : mapPoints (a ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
      deodharPrefixLift G (expression.take n.val) n.val) q =
        reductivePointsEquiv G (deodharPrefix G expression p n.val))
    (ht : mapPoints (a ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) q =
        additivePointsEquiv K t) :
    mapPoints (a ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) q =
      flagVarietyPointsEquiv G (flagProjection G
        (deodharPrefix G expression p n.val *
          gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) t *
          (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹)) := by
  let s : (additiveVariety K).toOver ⟶ (flagVariety G).toOver :=
    (simpleCellIso G (word[n.val]'n.isLt)).hom ≫
      schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt))
  have hs : mapPoints (a ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫ s) q =
        mapPoints s (additivePointsEquiv K t) := by
    have hc := mapPoints_comp (X := Q) (Y := additiveVariety K) (Z := flagVariety G)
      (a ≫ snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) s q
    simpa only [Category.assoc] using hc.trans (congrArg (mapPoints s) ht)
  have hmap := hm Q a q
  exact hmap.trans ((congrArg₂ (fun (g : (reductiveVariety G).points)
    (x : (flagVariety G).points) => g • x) hb hs).trans
      (frame_simple_action G (deodharPrefix G expression p n.val) (word[n.val]'n.isLt) t))


include hm in
private theorem fibre_raw (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (x : F.points) :
    ∃ p : Fin word.length → K,
      mapPoints (r.hom ≫ m ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) x =
      flagVarietyPointsEquiv G (flagProjection G
        (deodharPrefix G expression p n.val *
          gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt))
            ((additivePointsEquiv K).symm (mapPoints (r.hom ≫
              snd (deodharParameters G (expression.take n.val)).toOver
                (additiveVariety K).toOver) x)) *
          (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹)) := by
  let y := mapPoints (r.hom ≫
    fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) x
  obtain ⟨p, hp⟩ := exists_deodharPrefix_frame G expression n.val y
  refine ⟨p, ?_⟩
  have hb : mapPoints (r.hom ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
      deodharPrefixLift G (expression.take n.val) n.val) x =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) := by
    have hc := mapPoints_comp (X := F) (Y := deodharParameters G (expression.take n.val))
      (Z := reductiveVariety G)
      (r.hom ≫ fst (deodharParameters G (expression.take n.val)).toOver
        (additiveVariety K).toOver) (deodharPrefixLift G (expression.take n.val) n.val) x
    simpa only [Category.assoc] using hc.trans hp
  exact fibre_frame G expression n m hm F r.hom x p _ hb
    ((additivePointsEquiv K).apply_symm_apply _).symm

include hm in
/-- At an increasing step, the prescribed opposite cell requires the zero coordinate. -/
theorem positiveStep_fibre
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (x : F.points) :
    mapPoints (r.hom ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) x ∈
        Set.range (mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))) ↔
      mapPoints (r.hom ≫ snd (deodharParameters G (expression.take n.val)).toOver
        (additiveVariety K).toOver) x = additivePointsEquiv K 0 := by
  obtain ⟨p, hp⟩ := fibre_raw G expression n m hm F r x
  have hi := positiveStep_root G.rootBase expression n hn
  rw [List.get_eq_getElem] at hi
  have hv : expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1) =
      expression.prefixProd (weylCoxeterSystem G.rootBase) n.val *
        RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt) := by
    simpa only [weylCoxeterSystem_simple] using
      chosen_next (weylCoxeterSystem G.rootBase) expression n hn.2
  let c := mapPoints (r.hom ≫ snd (deodharParameters G (expression.take n.val)).toOver
    (additiveVariety K).toOver) x
  have hc := prefixFibre_ascent_zero_iff G expression hd p n.val (word[n.val]'n.isLt) hi
    ((additivePointsEquiv K).symm c)
  have hs := congrArg (fun v : G.weylGroup =>
    Set.range (mapPoints (oppositeSchubertCellInclusion G v))) hv
  have hmem := congrArg₂ (fun (z : (flagVariety G).points) (S : Set (flagVariety G).points) =>
    z ∈ S) hp hs
  apply (Iff.of_eq hmem).trans (hc.trans ?_)
  constructor
  · intro ht
    exact ((additivePointsEquiv K).apply_symm_apply c).symm.trans
      (congrArg (additivePointsEquiv K) ht)
  · intro ht
    simpa only [Equiv.symm_apply_apply] using congrArg (additivePointsEquiv K).symm ht

include hm in
/-- At a decreasing step, every additive coordinate has the prescribed opposite cell. -/
theorem negativeStep_fibre
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (x : F.points) :
    mapPoints (r.hom ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) x ∈
        Set.range (mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))) := by
  obtain ⟨p, hp⟩ := fibre_raw G expression n m hm F r x
  have hi := negativeStep_root G.rootBase expression n hn
  rw [List.get_eq_getElem] at hi
  have hv : expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1) =
      expression.prefixProd (weylCoxeterSystem G.rootBase) n.val *
        RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt) := by
    simpa only [weylCoxeterSystem_simple] using
      chosen_next (weylCoxeterSystem G.rootBase) expression n hn.2.symm
  have hc := prefixFibre_descent G expression hd p n.val (word[n.val]'n.isLt) hi
    ((additivePointsEquiv K).symm (mapPoints (r.hom ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) x))
  have hs := congrArg (fun v : G.weylGroup =>
    Set.range (mapPoints (oppositeSchubertCellInclusion G v))) hv
  exact Eq.mpr (congrArg₂
    (fun (z : (flagVariety G).points) (S : Set (flagVariety G).points) => z ∈ S) hp hs) hc

include hm in
/-- At an omitted step, the prescribed opposite cell requires a nonzero coordinate. -/
theorem equalStep_fibre
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (x : F.points) :
    mapPoints (r.hom ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) x ∈
        Set.range (mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))) ↔
      (additivePointsEquiv K).symm (mapPoints (r.hom ≫
        snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) x) ≠
          0 := by
  obtain ⟨p, hp⟩ := fibre_raw G expression n m hm F r x
  have hi := equalStep_root G.rootBase expression hd n hn
  rw [List.get_eq_getElem] at hi
  have hc := prefixFibre_ascent_nonzero_iff G expression hd p n.val (word[n.val]'n.isLt) hi
    ((additivePointsEquiv K).symm (mapPoints (r.hom ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) x))
  have hs := congrArg (fun v : G.weylGroup =>
    Set.range (mapPoints (oppositeSchubertCellInclusion G v))) hn.symm
  have hmem := congrArg₂ (fun (z : (flagVariety G).points) (S : Set (flagVariety G).points) =>
    z ∈ S) hp hs
  exact (Iff.of_eq hmem).trans hc

end
end SchubertGeometry
