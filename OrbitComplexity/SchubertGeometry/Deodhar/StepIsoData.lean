import OrbitComplexity.SchubertGeometry.Deodhar.StepMapFlags
import OrbitComplexity.SchubertGeometry.Deodhar.StepMapFibres
import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import OrbitComplexity.GroupActions.Varieties.ProductImmersions
import TauCeti.AlgebraicGeometry.Group.Smooth


/-! # Component charts from coordinate images

Coordinate maps with the same reduced image give component isomorphisms.
-/
open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
private theorem iso_left {S : Scheme} {X Y : Over S} (e : X ≅ Y) :
    IsIso e.hom.left := by
  change IsIso ((Over.forget S).map e.hom)
  infer_instance

private theorem section_pre {S : Scheme} {P X Y D : Over S}
    (e : P ≅ X) (z : X ⟶ Y) (c : X ⊗ Y ⟶ D)
    [IsSeparated Y.hom] [IsPreimmersion c.left] :
    IsPreimmersion ((e.hom ≫ lift (𝟙 X) z) ≫ c).left := by
  have := tensorSection_isClosed X Y z
  have := iso_left e
  change IsPreimmersion ((e.hom.left ≫ (lift (𝟙 X) z).left) ≫ c.left)
  infer_instance

private theorem iso_pre {S : Scheme} {P X D : Over S}
    (e : P ≅ X) (c : X ⟶ D) [IsPreimmersion c.left] :
    IsPreimmersion (e.hom ≫ c).left := by
  have := iso_left e
  change IsPreimmersion (e.hom.left ≫ c.left)
  infer_instance

private theorem factor_pre {S : Scheme} {P X Y Y' D : Over S}
    (e : P ≅ X ⊗ Y') (v : Y' ⟶ Y) (c : X ⊗ Y ⟶ D)
    (hv : IsOpenImmersion v.left) [IsPreimmersion c.left] :
    IsPreimmersion ((e.hom ≫ (𝟙 X ⊗ₘ v)) ≫ c).left := by
  have := hv
  have := iso_left e
  have : IsOpenImmersion (𝟙 X : X ⟶ X).left := by change IsOpenImmersion (𝟙 X.left); infer_instance
  have := tensorHom_isOpen (𝟙 X) v
  change IsPreimmersion ((e.hom.left ≫ (𝟙 X ⊗ₘ v).left) ≫ c.left)
  infer_instance

private def imageData {K : Type u} [Field K] [IsAlgClosed K]
    {A D Y : Variety K} (f : A.toOver ⟶ Y.toOver) (i : D.toOver ⟶ Y.toOver)
    [IsPreimmersion f.left] [IsPreimmersion i.left]
    (h : Set.range (mapPoints f) = Set.range (mapPoints i)) :
    {e : A.toOver ≅ D.toOver // e.hom ≫ i = f} :=
  ⟨pointImageIso f i h, pointImageIso_hom_comp f i h⟩

private theorem flag_comp {C : Type*} [Category C] {A D Y Z : C}
    (e : A ≅ D) (i : D ⟶ Y) (f : A ⟶ Y) (j : Y ⟶ Z)
    (h : e.hom ≫ i = f) : e.hom ≫ i ≫ j = f ≫ j := by
  rw [← Category.assoc, h]

private theorem cancel_factor {C : Type*} [Category C] {A B F R Y : C}
    (e : A ⟶ B) (z : B ⟶ R) (r : F ≅ R) (m : R ⟶ Y) :
    (e ≫ z ≫ r.inv) ≫ (r.hom ≫ m) = (e ≫ z) ≫ m := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem additive_smooth {K : Type u} [Field K] [IsAlgClosed K] :
    Smooth (additiveVariety K).toSpec :=
  TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced
    (additiveVariety K).toSpec

/-- The additive group product is a reduced finite-type variety. -/
def additiveProduct {K : Type u} [Field K] [IsAlgClosed K]
    (X : Variety K) : Variety K := by
  have := additive_smooth (K := K)
  exact smoothProductVariety (additiveVariety K) X

private def productSwap {C : Type*} [Category C] [CartesianMonoidalCategory C] (X Y : C) :
    X ⊗ Y ≅ Y ⊗ X where
  hom := lift (snd X Y) (fst X Y)
  inv := lift (snd Y X) (fst Y X)
  hom_inv_id := by apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by apply CartesianMonoidalCategory.hom_ext <;> simp

/-- The additive product has the expected Cartesian object over the field. -/
def additiveProductIso {K : Type u} [Field K] [IsAlgClosed K]
    (X : Variety K) : (additiveProduct X).toOver ≅ X.toOver ⊗ (additiveVariety K).toOver :=
  productSwap (additiveVariety K).toOver X.toOver

private def flagImageData {K : Type u} [Field K] [IsAlgClosed K]
    {A D Y Z : Variety K} (f : A.toOver ⟶ Y.toOver) (i : D.toOver ⟶ Y.toOver)
    (j : Y.toOver ⟶ Z.toOver) (p : A.toOver ⟶ Z.toOver)
    [IsPreimmersion f.left] [IsPreimmersion i.left]
    (h : Set.range (mapPoints f) = Set.range (mapPoints i)) (hflag : f ≫ j = p) :
    {e : A.toOver ≅ D.toOver // e.hom ≫ i ≫ j = p} :=
  let e := imageData f i h
  ⟨e.val, (flag_comp e.val i f j e.property).trans hflag⟩

attribute [local irreducible] deodharParameters deodharPositiveStepIso
  deodharNegativeStepIso deodharEqualStepIso imageData flagImageData

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

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
/-- The zero-coordinate preimmersion identifies the next intrinsic component. -/
theorem positiveIsoData
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression)
    [IsPreimmersion m.left]
    (hrange : Set.range (mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := wordCell G word (n.val + 1)) (((deodharPositiveStepIso G expression n hn).hom ≫ lift
        (𝟙 (deodharParameters G (expression.take n.val)).toOver) (toUnit (deodharParameters G
        (expression.take n.val)).toOver ≫ (additiveVariety K).pointsEquivOverHom
        (additivePointsEquiv K 0))) ≫ m)) =
        Set.range (mapPoints (X := deodharPrefixComponent G expression hred (n.val + 1))
          (Y := wordCell G word (n.val + 1)) (deodharPrefixInclusion G expression hred (n.val +
            1)))) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅ (deodharPrefixComponent G
      expression hred (n.val + 1)).toOver,
      e.hom ≫ (deodharPrefixInclusion G expression hred (n.val + 1)) ≫ (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take (n.val + 1)))) = (deodharPrefixMorphism G
        (expression.take (n.val + 1)) (n.val + 1)) := by
  have : IsPreimmersion (deodharPrefixInclusion G expression hred (n.val + 1)).left := by
    dsimp only [deodharPrefixInclusion]
    infer_instance
  have : IsSeparated (additiveVariety K).toOver.hom := by
    change IsSeparated (additiveVariety K).toSpec
    infer_instance
  have : IsPreimmersion (((deodharPositiveStepIso G expression n hn).hom ≫ lift (𝟙
    (deodharParameters G (expression.take n.val)).toOver) (toUnit (deodharParameters G
    (expression.take n.val)).toOver ≫ (additiveVariety K).pointsEquivOverHom (additivePointsEquiv
    K 0))) ≫ m).left :=
    section_pre (deodharPositiveStepIso G expression n hn) (toUnit (deodharParameters G
      (expression.take n.val)).toOver ≫ (additiveVariety K).pointsEquivOverHom
      (additivePointsEquiv K 0)) m
  let d := flagImageData (A := deodharParameters G (expression.take (n.val + 1)))
    (D := deodharPrefixComponent G expression hred (n.val + 1)) (Y := wordCell G word (n.val + 1))
    (Z := flagVariety G) (((deodharPositiveStepIso G expression n hn).hom ≫ lift (𝟙
      (deodharParameters G (expression.take n.val)).toOver) (toUnit (deodharParameters G
      (expression.take n.val)).toOver ≫ (additiveVariety K).pointsEquivOverHom
      (additivePointsEquiv K 0))) ≫ m) (deodharPrefixInclusion G expression hred (n.val + 1))
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
      (deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1)) hrange
    (positiveStep_flag G expression n m hm hn)
  exact ⟨d.val, d.property⟩



include hm in
/-- The full additive preimmersion identifies the next intrinsic component. -/
theorem negativeIsoData
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    [IsPreimmersion m.left]
    (hrange : Set.range (mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := wordCell G word (n.val + 1)) ((deodharNegativeStepIso G expression n hn).hom ≫ m)) =
        Set.range (mapPoints (X := deodharPrefixComponent G expression hred (n.val + 1))
          (Y := wordCell G word (n.val + 1)) (deodharPrefixInclusion G expression hred (n.val +
            1)))) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅ (deodharPrefixComponent G
      expression hred (n.val + 1)).toOver,
      e.hom ≫ (deodharPrefixInclusion G expression hred (n.val + 1)) ≫ (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take (n.val + 1)))) = (deodharPrefixMorphism G
        (expression.take (n.val + 1)) (n.val + 1)) := by
  have : IsPreimmersion (deodharPrefixInclusion G expression hred (n.val + 1)).left := by
    dsimp only [deodharPrefixInclusion]
    infer_instance
  have : IsPreimmersion ((deodharNegativeStepIso G expression n hn).hom ≫ m).left :=
    iso_pre (deodharNegativeStepIso G expression n hn) m
  let d := flagImageData (A := deodharParameters G (expression.take (n.val + 1)))
    (D := deodharPrefixComponent G expression hred (n.val + 1)) (Y := wordCell G word (n.val + 1))
    (Z := flagVariety G) ((deodharNegativeStepIso G expression n hn).hom ≫ m)
      (deodharPrefixInclusion G expression hred (n.val + 1))
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
      (deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1)) hrange
    (negativeStep_flag G expression n m hm hn)
  exact ⟨d.val, d.property⟩



include hm in
/-- The punctured-coordinate preimmersion identifies the next intrinsic component. -/
theorem equalIsoData
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression)
    [IsPreimmersion m.left]
    (hrange : Set.range (mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := wordCell G word (n.val + 1)) (((deodharEqualStepIso G expression n hn).hom ≫ (𝟙
        (deodharParameters G (expression.take n.val)).toOver ⊗ₘ ((puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K)))) ≫ m)) =
        Set.range (mapPoints (X := deodharPrefixComponent G expression hred (n.val + 1))
          (Y := wordCell G word (n.val + 1)) (deodharPrefixInclusion G expression hred (n.val +
            1)))) :
    ∃ e : (deodharParameters G (expression.take (n.val + 1))).toOver ≅ (deodharPrefixComponent G
      expression hred (n.val + 1)).toOver,
      e.hom ≫ (deodharPrefixInclusion G expression hred (n.val + 1)) ≫ (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take (n.val + 1)))) = (deodharPrefixMorphism G
        (expression.take (n.val + 1)) (n.val + 1)) := by
  have : IsPreimmersion (deodharPrefixInclusion G expression hred (n.val + 1)).left := by
    dsimp only [deodharPrefixInclusion]
    infer_instance
  have := iso_left (puncturedAdditiveInvIso K)
  have hv : IsOpenImmersion ((puncturedAdditiveInvIso K).hom ≫ (additiveVariety K).openInclusion
    (additiveNonzero K)).left := by
    change IsOpenImmersion ((puncturedAdditiveInvIso K).hom.left ≫
      ((additiveVariety K).openInclusion (additiveNonzero K)).left)
    infer_instance
  have : IsPreimmersion (((deodharEqualStepIso G expression n hn).hom ≫ (𝟙 (deodharParameters G
    (expression.take n.val)).toOver ⊗ₘ ((puncturedAdditiveInvIso K).hom ≫ (additiveVariety
    K).openInclusion (additiveNonzero K)))) ≫ m).left :=
    factor_pre (deodharEqualStepIso G expression n hn) ((puncturedAdditiveInvIso K).hom ≫
      (additiveVariety K).openInclusion (additiveNonzero K)) m hv
  let d := flagImageData (A := deodharParameters G (expression.take (n.val + 1)))
    (D := deodharPrefixComponent G expression hred (n.val + 1)) (Y := wordCell G word (n.val + 1))
    (Z := flagVariety G) (((deodharEqualStepIso G expression n hn).hom ≫ (𝟙 (deodharParameters G
      (expression.take n.val)).toOver ⊗ₘ ((puncturedAdditiveInvIso K).hom ≫ (additiveVariety
      K).openInclusion (additiveNonzero K)))) ≫ m) (deodharPrefixInclusion G expression hred
      (n.val + 1))
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n.val + 1))))
      (deodharPrefixMorphism G (expression.take (n.val + 1)) (n.val + 1)) hrange
    (equalStep_flag G expression n m hm hn)
  exact ⟨d.val, d.property⟩



end
end SchubertGeometry.Deodhar
