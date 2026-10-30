import OrbitComplexity.SchubertGeometry.Deodhar.WordCharts
import OrbitComplexity.SchubertGeometry.Deodhar.StepIsomorphisms
import OrbitComplexity.GroupActions.Varieties.PullbackImages


/-! # Extension of component charts

Cartesian word-cell coordinates extend a parameter chart by one simple reflection.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupActions GroupActions.Variety
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
variable {K : Type u} [Field K] {X D B : Variety K}
  {A : Over (Spec (CommRingCat.of K))}

/-- The right map of a cartesian square is a preimmersion when its base map is. -/
private theorem cartesian_pre (f : X.toOver ⟶ B.toOver) (q : D.toOver ⟶ B.toOver)
    (a : A ⟶ X.toOver) (m : A ⟶ D.toOver) (h : IsPullback a m f q)
    [IsPreimmersion f.left] : IsPreimmersion m.left := by
  have hp := (Over.forget (Spec (CommRingCat.of K))).map_isPullback h
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) hp (inferInstanceAs (IsPreimmersion
    f.left))

/-- A variety model of a cartesian square has the prescribed rational-point image. -/
private theorem cartesian_range (f : X.toOver ⟶ B.toOver) (q : D.toOver ⟶ B.toOver)
    (a : A ⟶ X.toOver) (m : A ⟶ D.toOver) (h : IsPullback a m f q)
    (P : Variety K) (r : P.toOver ≅ A) :
    Set.range (mapPoints (X := P) (Y := D) (r.hom ≫ m)) =
      (mapPoints (X := D) (Y := B) q) ⁻¹'
        Set.range (mapPoints (X := X) (Y := B) f) := by
  have hr := pullback_points_range f q (r ≪≫ h.isoPullback)
  simpa only [Iso.trans_hom, Category.assoc, h.isoPullback_hom_snd] using hr

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u

private theorem replace_preimage {α β : Type*} {A : Set α} {f : α → β} {S T : Set β}
    (h : A = f ⁻¹' S) (hST : S = T) : A = f ⁻¹' T :=
  h.trans (congrArg (fun N : Set β => f ⁻¹' N) hST)

attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso additiveProduct additiveProductIso
  wordCellExtensionIso wordCellStep

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
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
  (f : (deodharParameters G (expression.take n.val)).toOver ⟶
    (wordCell G word n.val).toOver)
  [IsPreimmersion f.left]
  (hpb : IsPullback
    (fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver)
    m f (wordCellStep G word hred n.val))
  (hfrange : Set.range (mapPoints
    (X := deodharParameters G (expression.take n.val)) (Y := wordCell G word n.val) f) =
    Set.range (mapPoints (X := deodharPrefixComponent G expression hred n.val)
      (Y := wordCell G word n.val) (deodharPrefixInclusion G expression hred n.val)))


include hm hd hpb hfrange in
/-- A cartesian coordinate map extends the preceding intrinsic component. -/
private theorem successorOfSquare :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  have : IsPreimmersion m.left := cartesian_pre
    (X := deodharParameters G (expression.take n.val))
    (D := wordCell G word (n.val + 1)) (B := wordCell G word n.val)
    (A := (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) f (wordCellStep G word hred n.val)
    (fst (deodharParameters G (expression.take n.val)).toOver
      (additiveVariety K).toOver) m hpb
  let F := additiveProduct (deodharParameters G (expression.take n.val))
  let r := additiveProductIso (deodharParameters G (expression.take n.val))
  have hfull := replace_preimage (cartesian_range
    (X := deodharParameters G (expression.take n.val))
    (D := wordCell G word (n.val + 1)) (B := wordCell G word n.val)
    (A := (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) f (wordCellStep G word hred n.val)
    (fst (deodharParameters G (expression.take n.val)).toOver
      (additiveVariety K).toOver) m hpb F r) hfrange
  exact stepCases G expression n m hm hred hd F r hfull


end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] deodharParameters
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)


/-- Cartesian chart data give the next intrinsic component. -/
private theorem successorOfChart
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (n : Fin word.length)
    (f : (deodharParameters G (expression.take n.val)).toOver ⟶
      (wordCell G word n.val).toOver)
    [IsPreimmersion f.left]
    (hfrange : Set.range (mapPoints
      (X := deodharParameters G (expression.take n.val)) (Y := wordCell G word n.val) f) =
      Set.range (mapPoints (X := deodharPrefixComponent G expression hred n.val)
        (Y := wordCell G word n.val) (deodharPrefixInclusion G expression hred n.val)))
    (hchart : ∃ m : (deodharParameters G (expression.take n.val)).toOver ⊗
        (additiveVariety K).toOver ⟶ (wordCell G word (n.val + 1)).toOver,
      (∀ (Q : Variety K)
        (a : Q.toOver ⟶ (deodharParameters G (expression.take n.val)).toOver ⊗
          (additiveVariety K).toOver) (q : Q.points),
        mapPoints (X := Q) (Y := flagVariety G)
          (a ≫ m ≫ schubertCellInclusion G
            (simpleWeylWord G.rootBase (word.take (n.val + 1)))) q =
          mapPoints (X := Q) (Y := reductiveVariety G)
            (a ≫ fst (deodharParameters G (expression.take n.val)).toOver
              (additiveVariety K).toOver ≫ deodharPrefixLift G (expression.take n.val) n.val) q •
          mapPoints (X := Q) (Y := flagVariety G)
            (a ≫ snd (deodharParameters G (expression.take n.val)).toOver
              (additiveVariety K).toOver ≫ (simpleCellIso G (word[n.val]'n.isLt)).hom ≫
                schubertCellInclusion G
                  (RootPairing.weylGroup.ofIdx G.rootSystem (word[n.val]'n.isLt))) q) ∧
      IsPullback
        (fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver)
        m f (wordCellStep G word hred n.val)) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  obtain ⟨m, hm, hpb⟩ := hchart
  exact successorOfSquare G expression n m hm hred hd f hpb hfrange

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] deodharParameters
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)


/-- A preceding parameter chart extends to the next intrinsic component. -/
private theorem successorExists
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (n : Fin word.length)
    (f : (deodharParameters G (expression.take n.val)).toOver ⟶
      (wordCell G word n.val).toOver)
    (hf : f ≫ schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n.val)) =
      deodharPrefixMorphism G (expression.take n.val) n.val)
    [IsPreimmersion f.left]
    (hfrange : Set.range (mapPoints
      (X := deodharParameters G (expression.take n.val)) (Y := wordCell G word n.val) f) =
      Set.range (mapPoints (X := deodharPrefixComponent G expression hred n.val)
        (Y := wordCell G word n.val) (deodharPrefixInclusion G expression hred n.val))) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n.val + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n.val + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))) =
          deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1) := by
  have hg : deodharPrefixLift G (expression.take n.val) n.val ≫
      flagQuotientMorphism G = f ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n.val)) :=
    (deodharPrefixLift_projection G (expression.take n.val) n.val).trans hf.symm
  exact successorOfChart G expression hred hd n f hfrange
    (wordChartExists G word n.val n.isLt
      (wordCell_ascent G word hred n.val n.isLt)
      (deodharParameters G (expression.take n.val)) f
      (deodharPrefixLift G (expression.take n.val) n.val) hg hred)

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] deodharParameters
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)


/-- A preceding parameter chart extends to the next intrinsic component. -/
theorem successorNatExists
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (n : ℕ) (hn : n < word.length)
    (f : (deodharParameters G (expression.take n)).toOver ⟶
      (wordCell G word n).toOver)
    (hf : f ≫ schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)) =
      deodharPrefixMorphism G (expression.take n) n)
    [IsPreimmersion f.left]
    (hfrange : Set.range (mapPoints
      (X := deodharParameters G (expression.take n)) (Y := wordCell G word n) f) =
      Set.range (mapPoints (X := deodharPrefixComponent G expression hred n)
        (Y := wordCell G word n) (deodharPrefixInclusion G expression hred n))) :
    ∃ e : (deodharParameters G (expression.take (n + 1))).toOver ≅
      (deodharPrefixComponent G expression hred (n + 1)).toOver,
      e.hom ≫ deodharPrefixInclusion G expression hred (n + 1) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1))) =
          deodharPrefixMorphism G (expression.take (n + 1)) (n + 1) := by
  exact successorExists G expression hred hd ⟨n, hn⟩ f hf hfrange

end
end SchubertGeometry.Deodhar
