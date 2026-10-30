import OrbitComplexity.SchubertGeometry.Deodhar.StepMapFibres
import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.GroupActions.Varieties.ProductImages
/-! # Images of the three Deodhar parameter steps

The zero section, punctured reciprocal factor, and full additive factor cut out the successor
component after imposing the preceding component condition.
-/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u

attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso

private theorem filtered_range {K : Type u} [Field K] {A F Y : Variety K}
    (v : A.toOver ⟶ F.toOver) (m : F.toOver ⟶ Y.toOver) (S : Set Y.points)
    (hv : Set.range (mapPoints v) = {x | mapPoints m x ∈ S}) :
    Set.range (mapPoints (v ≫ m)) = Set.range (mapPoints m) ∩ S := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    have ha : mapPoints v a ∈ Set.range (mapPoints v) := ⟨a, rfl⟩
    have hs : mapPoints m (mapPoints v a) ∈ S := by
      exact Eq.mp (congrArg (fun T : Set F.points => mapPoints v a ∈ T) hv) ha
    rw [mapPoints_comp]
    exact ⟨⟨mapPoints v a, rfl⟩, hs⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    have hvx : x ∈ Set.range (mapPoints v) :=
      Eq.mpr (congrArg (fun T : Set F.points => x ∈ T) hv) hx
    obtain ⟨a, rfl⟩ := hvx
    exact ⟨a, mapPoints_comp v m a⟩

private theorem filtered_comp_range {K : Type u} [Field K]
    {A F Y Z : Variety K}
    {R : Over (Spec (CommRingCat.of K))} (v : A.toOver ⟶ F.toOver)
    (r : F.toOver ⟶ R) (m : R ⟶ Y.toOver)
    (i : Y.toOver ⟶ Z.toOver) (T : Set Z.points)
    (hv : Set.range (mapPoints v) = {x | mapPoints (r ≫ m ≫ i) x ∈ T}) :
    Set.range (mapPoints (v ≫ (r ≫ m))) =
      Set.range (mapPoints (r ≫ m)) ∩ {y | mapPoints i y ∈ T} := by
  apply filtered_range
  ext x
  have hm : mapPoints (r ≫ m ≫ i) x = mapPoints i (mapPoints (r ≫ m) x) :=
    (congrArg (fun t : F.toOver ⟶ Z.toOver => mapPoints t x)
      (Category.assoc r m i)).symm.trans (mapPoints_comp (r ≫ m) i x)
  exact (Set.ext_iff.mp hv x).trans (Iff.of_eq (congrArg (fun z => z ∈ T) hm))

private theorem preiso_range {K : Type u} [Field K] {A B F : Variety K}
    (e : A.toOver ≅ B.toOver) (f : B.toOver ⟶ F.toOver) :
    Set.range (mapPoints (e.hom ≫ f)) = Set.range (mapPoints f) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨mapPoints e.hom a, (mapPoints_comp e.hom f a).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (pointsHomeomorph e).surjective b
    exact ⟨a, mapPoints_comp e.hom f a⟩

private theorem preimage_raw {α β : Type*} {A : Set α} (f : α → β) (S : Set β)
    (h : A = f ⁻¹' S) : A = (fun x => S (f x)) := h

private theorem finish_range {α : Type*} {A B C D T : Set α}
    (hAB : A = B ∩ T) (hBC : B = C)
    (hCD : (fun x => C x ∧ T x) = D) : A = D :=
  hAB.trans ((congrArg (fun B : Set α => fun x => B x ∧ T x) hBC).trans hCD)

private theorem preiso_surjective {K : Type u} [Field K] {A F : Variety K}
    {R : Over (Spec (CommRingCat.of K))} (e : A.toOver ≅ R) (r : F.toOver ≅ R) :
    Function.Surjective (mapPoints (X := A) (Y := F) (e.hom ≫ r.inv)) :=
  (pointsHomeomorph (e ≪≫ r.symm)).surjective

private theorem surjective_filter {α β : Type*} (f : α → β) (Q : β → Prop)
    (hf : Function.Surjective f) (hq : ∀ x, Q x) : Set.range f = Q :=
  Set.ext (fun x => iff_of_true (hf x) (hq x))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem inclusion_points (n : ℕ) (x : (wordCell G word n).points) :
    mapPoints (X := wordCell G word n) (Y := flagVariety G)
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n))) x =
    mapPoints (X := schubertCell G (simpleWeylWord G.rootBase (word.take n)))
      (Y := flagVariety G)
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n))) x := by
  apply Subtype.ext
  rfl

private theorem word_successor_mem
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ)
    (x : (wordCell G word (n + 1)).points) :
    x ∈ Set.range (mapPoints (deodharPrefixInclusion G expression hred (n + 1))) ↔
    mapPoints (wordCellStep G word hred n) x ∈
      Set.range (mapPoints (deodharPrefixInclusion G expression hred n)) ∧
    mapPoints (X := wordCell G word (n + 1)) (Y := flagVariety G)
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) x ∈
        Set.range (mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) (n + 1)))) := by
  have hi := congrArg (fun q : (flagVariety G).points => q ∈
    Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n + 1)))))
      (inclusion_points G (word := word) (n + 1) x).symm
  exact (mem_deodharPrefix_succ G expression hred n x).trans
    (and_congr Iff.rfl (Iff.of_eq hi))

private theorem successor_range
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ) :
    type_of% (Set.ext (fun y : (wordCell G word (n + 1)).points =>
      (word_successor_mem G expression hred n y).symm)) :=
  Set.ext (fun y : (wordCell G word (n + 1)).points =>
    (word_successor_mem G expression hred n y).symm)

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
private theorem positive_filter
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (Set.ext (fun x : F.points =>
      (Set.ext_iff.mp ((preiso_range (deodharPositiveStepIso G expression n hn)
        (lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
          (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
            (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ r.inv)).trans
        (zeroSection_points_range (deodharParameters G (expression.take n.val)) F r)) x).trans
          (positiveStep_fibre G expression n m hm hd hn F r x).symm)) :=
    Set.ext (fun x : F.points =>
      (Set.ext_iff.mp ((preiso_range (deodharPositiveStepIso G expression n hn)
        (lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
          (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
            (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ r.inv)).trans
        (zeroSection_points_range (deodharParameters G (expression.take n.val)) F r)) x).trans
          (positiveStep_fibre G expression n m hm hd hn F r x).symm)

include hm in
private theorem positive_image
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharPositiveStepIso G expression n hn).hom ≫
      lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
        (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
          (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1))))) (positive_filter G
        expression n m hm hd hn F r)) :=
  filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharPositiveStepIso G expression n hn).hom ≫
      lift (𝟙 (deodharParameters G (expression.take n.val)).toOver)
        (toUnit (deodharParameters G (expression.take n.val)).toOver ≫
          (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1))))) (positive_filter G
        expression n m hm hd hn F r)

include hm in
/-- The increasing-step parameter image is the next intrinsic component. -/
theorem positiveRange
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver)
    (hfull : Set.range (mapPoints (X := F) (Y := wordCell G word (n.val + 1))
        (r.hom ≫ m)) =
      (mapPoints (X := wordCell G word (n.val + 1))
        (Y := wordCell G word n.val) (wordCellStep G word hred n.val)) ⁻¹'
        Set.range (mapPoints (deodharPrefixInclusion G expression hred n.val))) :
    type_of% (finish_range (positive_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
      (successor_range G expression hred n.val)) :=
  finish_range (positive_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
    (successor_range G expression hred n.val)

include hm in
private theorem negative_filter
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (surjective_filter (mapPoints (X := deodharParameters G
      (expression.take (n.val + 1))) (Y := F)
        ((deodharNegativeStepIso G expression n hn).hom ≫ r.inv)) _
      (preiso_surjective (deodharNegativeStepIso G expression n hn) r)
      (negativeStep_fibre G expression n m hm hd hn F r)) :=
  surjective_filter (mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := F) ((deodharNegativeStepIso G expression n hn).hom ≫ r.inv)) _
      (preiso_surjective (deodharNegativeStepIso G expression n hn) r)
      (negativeStep_fibre G expression n m hm hd hn F r)

include hm in
private theorem equal_filter
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (Set.ext (fun x : F.points =>
      (Set.ext_iff.mp (reciprocalFactor_points_range
        (deodharParameters G (expression.take n.val)) F
        (deodharParameters G (expression.take (n.val + 1))) r
        (deodharEqualStepIso G expression n hn)) x).trans
          (equalStep_fibre G expression n m hm hd hn F r x).symm)) :=
  Set.ext (fun x : F.points =>
    (Set.ext_iff.mp (reciprocalFactor_points_range
      (deodharParameters G (expression.take n.val)) F
      (deodharParameters G (expression.take (n.val + 1))) r
      (deodharEqualStepIso G expression n hn)) x).trans
        (equalStep_fibre G expression n m hm hd hn F r x).symm)

include hm in
private theorem negative_image
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharNegativeStepIso G expression n hn).hom ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))))
    (negative_filter G expression n m hm hd hn F r)) :=
  filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharNegativeStepIso G expression n hn).hom ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))))
    (negative_filter G expression n m hm hd hn F r)

include hm in
/-- The decreasing-step parameter image is the next intrinsic component. -/
theorem negativeRange
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver)
    (hfull : Set.range (mapPoints (X := F) (Y := wordCell G word (n.val + 1))
        (r.hom ≫ m)) =
      (mapPoints (X := wordCell G word (n.val + 1))
        (Y := wordCell G word n.val) (wordCellStep G word hred n.val)) ⁻¹'
        Set.range (mapPoints (deodharPrefixInclusion G expression hred n.val))) :
    type_of% (finish_range (negative_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
      (successor_range G expression hred n.val)) :=
  finish_range (negative_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
      (successor_range G expression hred n.val)

include hm in
private theorem equal_image
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver) :
    type_of% (filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharEqualStepIso G expression n hn).hom ≫
      (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
        ((puncturedAdditiveInvIso K).hom ≫
          (additiveVariety K).openInclusion (additiveNonzero K))) ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))))
    (equal_filter G expression n m hm hd hn F r)) :=
  filtered_comp_range
    (A := deodharParameters G (expression.take (n.val + 1))) (F := F)
    (Y := wordCell G word (n.val + 1)) (Z := flagVariety G)
    ((deodharEqualStepIso G expression n hn).hom ≫
      (𝟙 (deodharParameters G (expression.take n.val)).toOver ⊗ₘ
        ((puncturedAdditiveInvIso K).hom ≫
          (additiveVariety K).openInclusion (additiveNonzero K))) ≫ r.inv) r.hom m
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
    (Set.range (mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) (n.val + 1)))))
    (equal_filter G expression n m hm hd hn F r)

include hm in
/-- The omitted-step parameter image is the next intrinsic component. -/
theorem equalRange
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) (F : Variety K)
    (r : F.toOver ≅ (deodharParameters G (expression.take n.val)).toOver ⊗
      (additiveVariety K).toOver)
    (hfull : Set.range (mapPoints (X := F) (Y := wordCell G word (n.val + 1))
        (r.hom ≫ m)) =
      (mapPoints (X := wordCell G word (n.val + 1))
        (Y := wordCell G word n.val) (wordCellStep G word hred n.val)) ⁻¹'
        Set.range (mapPoints (deodharPrefixInclusion G expression hred n.val))) :
    type_of% (finish_range (equal_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
      (successor_range G expression hred n.val)) :=
  finish_range (equal_image G expression n m hm hd hn F r) (preimage_raw _ _ hfull)
      (successor_range G expression hred n.val)

end
end SchubertGeometry.Deodhar
