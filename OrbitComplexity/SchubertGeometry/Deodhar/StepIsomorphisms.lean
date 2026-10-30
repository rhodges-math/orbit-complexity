import OrbitComplexity.SchubertGeometry.Deodhar.StepRanges
import OrbitComplexity.SchubertGeometry.Deodhar.StepIsoData


/-! # Three coordinate-step isomorphisms

Increasing, omitted, and decreasing steps give the next component chart.
-/
open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u

private theorem cancel_range {K : Type u} [Field K] {A F Y : Variety K}
    {B R : Over (Spec (CommRingCat.of K))} (e : A.toOver ⟶ B) (z : B ⟶ R)
    (r : F.toOver ≅ R) (m : R ⟶ Y.toOver) (D : Set Y.points)
    (h : Set.range (mapPoints ((e ≫ z ≫ r.inv) ≫ (r.hom ≫ m))) = D) :
    Set.range (mapPoints ((e ≫ z) ≫ m)) = D := by
  have he : (e ≫ z ≫ r.inv) ≫ (r.hom ≫ m) = (e ≫ z) ≫ m := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun f : A.toOver ⟶ Y.toOver => Set.range (mapPoints f)) he).symm.trans h

private theorem cancel_range' {K : Type u} [Field K] {A F Y : Variety K}
    {R : Over (Spec (CommRingCat.of K))} (e : A.toOver ⟶ R)
    (r : F.toOver ≅ R) (m : R ⟶ Y.toOver) (D : Set Y.points)
    (h : Set.range (mapPoints ((e ≫ r.inv) ≫ (r.hom ≫ m))) = D) :
    Set.range (mapPoints (e ≫ m)) = D := by
  have he : (e ≫ r.inv) ≫ (r.hom ≫ m) = e ≫ m := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun f : A.toOver ⟶ Y.toOver => Set.range (mapPoints f)) he).symm.trans h

attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso additiveProduct additiveProductIso

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (n : Fin word.length)
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
  [IsPreimmersion m.left]
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
  (F : Variety K)
  (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
    (additiveVariety K).toOver)
  (hfull : Set.range (mapPoints (X := F) (Y := wordCell G word (n.val + 1))
      (r.hom ≫ m)) =
    (mapPoints (X := wordCell G word (n.val + 1))
      (Y := wordCell G word n.val) (wordCellStep G word hred n.val)) ⁻¹'
      Set.range (mapPoints (deodharPrefixInclusion G expression hred n.val)))

include hm hd hfull in
/-- The zero-coordinate chart is isomorphic to the increasing-prefix component. -/
private theorem positiveIso
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  have hr := positiveRange G expression n m hm hred hd hn F r hfull
  have hrc := cancel_range (deodharPositiveStepIso G expression n hn).hom
    (lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
      (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
        (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0))) r m
    (Set.range (mapPoints (deodharPrefixInclusion G expression hred (n.val + 1)))) hr
  exact positiveIsoData G expression n m hm hred hn hrc

include hm hd hfull in
/-- The additive chart is isomorphic to the decreasing-prefix component. -/
private theorem negativeIso
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  have hr := negativeRange G expression n m hm hred hd hn F r hfull
  have hrc := cancel_range' (deodharNegativeStepIso G expression n hn).hom r m
    (Set.range (mapPoints (deodharPrefixInclusion G expression hred (n.val + 1)))) hr
  exact negativeIsoData G expression n m hm hred hn hrc

include hm hd hfull in
/-- The reciprocal punctured chart is isomorphic to the constant-prefix component. -/
private theorem equalIso
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  have hr := equalRange G expression n m hm hred hd hn F r hfull
  have hrc := cancel_range (deodharEqualStepIso G expression n hn).hom
    (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
      ((puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K))) r m
    (Set.range (mapPoints (deodharPrefixInclusion G expression hred (n.val + 1)))) hr
  exact equalIsoData G expression n m hm hred hn hrc

end
end SchubertGeometry.Deodhar

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso additiveProduct additiveProductIso

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (n : Fin word.length)
  (m : (deodharParameters G (expression.take n.val)).toOver ⊗
    (additiveVariety K).toOver ⟶ (wordCell G word (n.val + 1)).toOver)
  (hm : ∀ (Q : Variety K)
    (a : Q.toOver ⟶ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) (q : Q.points),
    mapPoints (X := Q) (Y := flagVariety G) (a ≫ m ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1)))) q =
      mapPoints (X := Q) (Y := reductiveVariety G) (a ≫ fst (deodharParameters G (expression.take
        n.val)).toOver
        (additiveVariety K).toOver ≫ deodharPrefixLift G (expression.take n.val) n.val) q •
      mapPoints (X := Q) (Y := flagVariety G) (a ≫ snd (deodharParameters G (expression.take
        n.val)).toOver
        (additiveVariety K).toOver ≫ (simpleCellIso G (word[n.val]'n.isLt)).hom ≫
        schubertCellInclusion G
          (RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt))) q)
  [IsPreimmersion m.left]
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
  (F : Variety K)
  (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
    (additiveVariety K).toOver)
  (hfull : Set.range (mapPoints (X := F) (Y := wordCell G word (n.val + 1))
      (r.hom ≫ m)) =
    (mapPoints (X := wordCell G word (n.val + 1))
      (Y := wordCell G word n.val) (wordCellStep G word hred n.val)) ⁻¹'
      Set.range (mapPoints (X := deodharPrefixComponent G expression hred n.val)
        (Y := wordCell G word n.val) (deodharPrefixInclusion G expression hred n.val)))



include hm hd hfull in
/-- The negative chart theorem accepts the explicit point bundles. -/
private theorem negativeTyped
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  exact negativeIso G expression n m hm hred hd F r hfull hn


include hm hd hfull in
/-- The positive chart theorem accepts the explicit point bundles. -/
private theorem positiveTyped
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  exact positiveIso G expression n m hm hred hd F r hfull hn


include hm hd hfull in
/-- The equal chart theorem accepts the explicit point bundles. -/
private theorem equalTyped
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  exact equalIso G expression n m hm hred hd F r hfull hn


include hm hd hfull in
/-- The three explicit point-coordinate charts give the successor component. -/
theorem stepCases :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  rcases mem_step_sets (weylCoxeterSystem G.rootBase) expression n with hp | he | hn
  · exact positiveTyped G expression n m hm hred hd F r hfull hp
  · exact equalTyped G expression n m hm hred hd F r hfull he
  · exact negativeTyped G expression n m hm hred hd F r hfull hn

end
end SchubertGeometry.Deodhar
