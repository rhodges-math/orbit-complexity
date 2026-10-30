import OrbitComplexity.SchubertGeometry.Deodhar.ParameterFrames
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.GroupActions.Varieties.CoordinateInversion
import OrbitComplexity.GroupActions.Varieties.AdditiveOpens

/-! # Flag morphisms for a parameter step -/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private theorem factor_fst {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Q X Y Z : C} (e : Q ⟶ X ⊗ Y) (v : Y ⟶ Z) :
    (e ≫ (𝟙 X ⊗ₘ v)) ≫ fst X Z = e ≫ fst X Y := by
  simp only [Category.assoc, tensorHom_fst, Category.comp_id]

private theorem factor_snd {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Q X Y Z : C} (e : Q ⟶ X ⊗ Y) (v : Y ⟶ Z) :
    (e ≫ (𝟙 X ⊗ₘ v)) ≫ snd X Z = (e ≫ snd X Y) ≫ v := by
  simp only [Category.assoc, tensorHom_snd]

private theorem constant_points {K : Type u} [Field K] (X Y : Variety K)
    (y : Y.points) (x : X.points) :
    mapPoints (toUnit X.toOver ≫ Y.pointsEquivOverHom y) x = y := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom x ≫ (toUnit X.toOver ≫ Y.pointsEquivOverHom y) = _
  rw [comp_toUnit_assoc]
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = 𝟙 _ := toUnit_unique _ _
  rw [hu, Category.id_comp]

attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem prefix_succ (p : Fin word.length → K) (n : Fin word.length) :
    deodharPrefix G expression p (n.val + 1) =
      deodharPrefix G expression p n.val * deodharStep G expression p n := by
  simp only [deodharPrefix]
  rw [List.prod_take_succ _ _ (by simpa only [List.length_ofFn] using n.isLt), List.getElem_ofFn]

private theorem positive_not_negative (n : Fin word.length)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    n ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression := by
  intro h
  have hlt := hn.1.length_lt_of_ne hn.2
  have hle := h.1.length_le
  omega

private theorem prefix_positive (p : Fin word.length → K) (n : Fin word.length)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    deodharPrefix G expression p (n.val + 1) =
      deodharPrefix G expression p n.val * (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹ := by
  classical
  have he : n ∉ equalSteps (weylCoxeterSystem G.rootBase) expression := hn.2
  rw [prefix_succ G expression p n]
  simp only [deodharStep, deodharRootElement, subwordStepPoint,
    positive_not_negative G expression n hn, he, ↓reduceIte, simpleRepresentative, one_mul]

private theorem prefix_negative (p : Fin word.length → K) (n : Fin word.length)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    deodharPrefix G expression p (n.val + 1) =
      deodharPrefix G expression p n.val *
        gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) (p n) *
          G.reflectionPoint (word[n.val]'n.isLt).val := by
  classical
  rw [prefix_succ G expression p n]
  simp only [deodharStep, deodharRootElement, subwordStepPoint, hn, ↓reduceIte,
    simpleRepresentative, inv_inv, mul_assoc]

private theorem prefix_equal (p : Fin word.length → K) (n : Fin word.length)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    deodharPrefix G expression p (n.val + 1) =
      deodharPrefix G expression p n.val *
        gaParameterPoint (G.negativeSimpleRootMap (word[n.val]'n.isLt)) (p n) := by
  classical
  have hneg : n ∉ negativeSteps (weylCoxeterSystem G.rootBase) expression :=
    fun h => h.2 hn.symm
  rw [prefix_succ G expression p n]
  simp only [deodharStep, deodharRootElement, subwordStepPoint, hneg, hn, ↓reduceIte, mul_one]

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

private theorem frame_flag (n : ℕ)
    (q : (deodharParameters G (expression.take n)).points) (g : G.points)
    (hg : mapPoints (deodharPrefixLift G (expression.take n) n) q = reductivePointsEquiv G g) :
    mapPoints (deodharPrefixMorphism G (expression.take n) n) q =
      flagVarietyPointsEquiv G (flagProjection G g) := by
  rw [← deodharPrefixLift_projection G (expression.take n) n, mapPoints_comp, hg,
    flagQuotientMorphism_points G g]

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
/-- The zero-coordinate step has the next prefix flag morphism. -/
theorem positiveStep_flag
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    ((deodharPositiveStepIso G expression n hn).hom ≫
      lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
        (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
          (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ m) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
        deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  apply mapPoints_injective (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := flagVariety G)
  funext q
  obtain ⟨p, hnew, hprev⟩ := deodharPositiveStep_frames G expression n hn q
  let a : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver ⊗ (additiveVariety K).toOver :=
    (deodharPositiveStepIso G expression n hn).hom ≫
      lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
        (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
          (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0))
  have hb : mapPoints (a ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
      deodharPrefixLift G (expression.take n.val) n.val) q =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) := by
    simpa only [a, Category.assoc, lift_fst_assoc, Category.id_comp] using hprev
  have ht : mapPoints (a ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) q =
        additivePointsEquiv K 0 := by
    let z := toUnit (deodharParameters G (expression.take n.val)).toOver ≫
      (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)
    have hc := mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := deodharParameters G (expression.take n.val)) (Z := additiveVariety K)
      (deodharPositiveStepIso G expression n hn).hom z q
    have hz := constant_points (deodharParameters G (expression.take n.val)) (additiveVariety K)
      (additivePointsEquiv K 0) (mapPoints (deodharPositiveStepIso G expression n hn).hom q)
    simpa only [a, z, Category.assoc, lift_snd] using hc.trans hz
  have hm := fibre_frame G expression n m hm
    (deodharParameters G (expression.take (n.val + 1))) a q p 0 hb ht
  have hr : deodharPrefix G expression p n.val *
      gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) (0 : K) *
        (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹ =
      deodharPrefix G expression p (n.val + 1) := by
    rw [gaParameterPoint_zero, mul_one, prefix_positive G expression p n hn]
  have hnflag := frame_flag G expression (n.val + 1) q
    (deodharPrefix G expression p (n.val + 1)) hnew
  have hc := hm.trans ((congrArg (fun g : G.points =>
    flagVarietyPointsEquiv G (flagProjection G g)) hr).trans hnflag.symm)
  simpa only [a, Category.assoc] using hc

include hm in
/-- The additive-coordinate step has the next prefix flag morphism. -/
theorem negativeStep_flag
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    ((deodharNegativeStepIso G expression n hn).hom ≫ m) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
        deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  apply mapPoints_injective (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := flagVariety G)
  funext q
  obtain ⟨p, hnew, hprev, hlast⟩ := deodharNegativeStep_frames G expression n hn q
  let a := (deodharNegativeStepIso G expression n hn).hom
  have hb : mapPoints (a ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
      deodharPrefixLift G (expression.take n.val) n.val) q =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) := by
    simpa only [a, Category.assoc] using hprev
  have ht : mapPoints (a ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) q =
        additivePointsEquiv K (p n) := by
    simpa only [a, Equiv.apply_symm_apply] using
      (congrArg (additivePointsEquiv K) hlast).symm
  have hmap := fibre_frame G expression n m hm
    (deodharParameters G (expression.take (n.val + 1))) a q p (p n) hb ht
  have hr : flagProjection G
      (deodharPrefix G expression p n.val *
        gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) (p n) *
          (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹) =
        flagProjection G (deodharPrefix G expression p (n.val + 1)) := by
    rw [prefix_negative G expression p n hn]
    exact (flag_reflection_eq_inv G (word[n.val]'n.isLt)
      (deodharPrefix G expression p n.val *
        gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) (p n))).symm
  have hnflag := frame_flag G expression (n.val + 1) q
    (deodharPrefix G expression p (n.val + 1)) hnew
  have hc := hmap.trans ((congrArg (flagVarietyPointsEquiv G) hr).trans hnflag.symm)
  simpa only [a, Category.assoc] using hc

include hm in
/-- The reciprocal omitted step has the next prefix flag morphism. -/
theorem equalStep_flag
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    ((deodharEqualStepIso G expression n hn).hom ≫
      (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
        ((puncturedAdditiveInvIso K).hom ≫
          (additiveVariety K).openInclusion (additiveNonzero K))) ≫ m) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
        deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  apply mapPoints_injective (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := flagVariety G)
  funext q
  obtain ⟨p, hnew, hprev, hlast⟩ := deodharEqualStep_frames G expression n hn q
  let b : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver :=
    (deodharEqualStepIso G expression n hn).hom ≫
      snd (deodharParameters G (expression.take n.val)).toOver
        ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver
  let q' := mapPoints b q
  let v : ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ⟶
      (additiveVariety K).toOver :=
    (puncturedAdditiveInvIso K).hom ≫
      (additiveVariety K).openInclusion (additiveNonzero K)
  let a : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver ⊗ (additiveVariety K).toOver :=
    (deodharEqualStepIso G expression n hn).hom ≫
      (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ v)
  have hb : mapPoints (a ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
      deodharPrefixLift G (expression.take n.val) n.val) q =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) := by
    have hfst := factor_fst (deodharEqualStepIso G expression n hn).hom v
    have hcomp : a ≫
        fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
          deodharPrefixLift G (expression.take n.val) n.val =
        ((deodharEqualStepIso G expression n hn).hom ≫
          fst (deodharParameters G (expression.take n.val)).toOver
            ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver) ≫
              deodharPrefixLift G (expression.take n.val) n.val := by
      rw [← Category.assoc]
      exact congrArg (fun t => t ≫ deodharPrefixLift G (expression.take n.val) n.val) hfst
    exact (congrArg (fun t => mapPoints t q) hcomp).trans hprev
  have hparam : p n = (additivePointsEquiv K).symm
      (mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) q') := by
    have hc := mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := (additiveVariety K).openSubvariety (additiveNonzero K))
      (Z := additiveVariety K) b
      ((additiveVariety K).openInclusion (additiveNonzero K)) q
    exact hlast.trans (congrArg (additivePointsEquiv K).symm hc)
  have hp : p n ≠ 0 := by
    have hmem : mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) q' ∈
        Set.range (mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))) :=
      ⟨q', rfl⟩
    rw [additiveNonzero_points] at hmem
    exact hparam ▸ hmem
  have ha : a ≫ snd (deodharParameters G (expression.take n.val)).toOver
      (additiveVariety K).toOver = b ≫ v := by
    exact factor_snd (deodharEqualStepIso G expression n hn).hom v
  have ht : mapPoints (a ≫
      snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) q =
        additivePointsEquiv K ((p n)⁻¹) := by
    rw [ha]
    have hc := mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := (additiveVariety K).openSubvariety (additiveNonzero K))
      (Z := additiveVariety K) b v q
    rw [hc]
    apply (additivePointsEquiv K).symm.injective
    change (additivePointsEquiv K).symm
      (mapPoints ((puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K)) q') = _
    rw [mapPoints_comp, puncturedAdditiveInvIso_points, ← hparam, Equiv.symm_apply_apply]
  have hmap := fibre_frame G expression n m hm
    (deodharParameters G (expression.take (n.val + 1))) a q p ((p n)⁻¹) hb ht
  have hr : flagProjection G
      (deodharPrefix G expression p n.val *
        gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) ((p n)⁻¹) *
          (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹) =
        flagProjection G (deodharPrefix G expression p (n.val + 1)) := by
    rw [prefix_equal G expression p n hn]
    have he := congrArg (fun z : flagPoints G => deodharPrefix G expression p n.val • z)
      (simpleRoot_flag_eq_negative G (word[n.val]'n.isLt) (inv_ne_zero hp))
    change flagProjection G (deodharPrefix G expression p n.val *
      (gaParameterPoint (G.simpleRootMap (word[n.val]'n.isLt)) ((p n)⁻¹) *
        (G.reflectionPoint (word[n.val]'n.isLt).val)⁻¹)) =
      flagProjection G (deodharPrefix G expression p n.val *
        gaParameterPoint (G.negativeSimpleRootMap (word[n.val]'n.isLt)) (((p n)⁻¹)⁻¹)) at he
    simpa only [mul_assoc, inv_inv] using he
  have hnflag := frame_flag G expression (n.val + 1) q
    (deodharPrefix G expression p (n.val + 1)) hnew
  have hc := hmap.trans ((congrArg (flagVarietyPointsEquiv G) hr).trans hnflag.symm)
  have hcomp :
      (((deodharEqualStepIso G expression n hn).hom ≫
        (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
          ((puncturedAdditiveInvIso K).hom ≫
            (additiveVariety K).openInclusion (additiveNonzero K)))) ≫ m) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
      a ≫ m ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) :=
    Category.assoc a m _
  exact (congrArg (fun t : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
    (flagVariety G).toOver => mapPoints t q) hcomp).trans hc

end
end SchubertGeometry
