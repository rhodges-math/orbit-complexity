import OrbitComplexity.SchubertGeometry.Deodhar.RelativeAction

/-! # Transport of relative simple-extension maps

Postcomposing a relative chart by a cell identification preserves its projection and
its multiplication formula whenever the identification commutes with those maps.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section

private theorem chart_project {C : Type*} [Category C] [HasPullbacks C]
    {A X Y D B : C} (f : X ⟶ B) (p : Y ⟶ B) (j : Y ⟶ D) (q : D ⟶ B)
    (h : j ≫ q = p) (a : A ⟶ pullback f p) (m : A ⟶ X)
    (hm : a ≫ pullback.fst f p = m) :
    (a ≫ pullback.snd f p ≫ j) ≫ q = m ≫ f := by
  have hp : (a ≫ pullback.snd f p ≫ j) ≫ q =
      (a ≫ pullback.fst f p) ≫ f := by
    simp only [Category.assoc, h, ← pullback.condition]
  exact hp.trans (congrArg (fun k : A ⟶ X => k ≫ f) hm)

private theorem chart_action {C : Type*} [Category C] {Z A P Y D F : C}
    (z : Z ⟶ A) (a : A ⟶ P) (p : P ⟶ Y) (j : Y ⟶ D) (l : D ⟶ F)
    (r : Y ⟶ F) (v : Z ⟶ F) (hj : j ≫ l = r)
    (ha : z ≫ (a ≫ p ≫ r) = v) : z ≫ (a ≫ p ≫ j ≫ l) = v :=
  (congrArg (fun k : Y ⟶ F => z ≫ (a ≫ p ≫ k)) hj).trans ha

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X D : GroupActions.Variety K) (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)
  (j : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver ⟶ D.toOver)

/-- A transported relative chart has the prescribed cell projection. -/
theorem rankOneLiftMap_projection (q : D.toOver ⟶ (schubertCell G w).toOver)
    (hj : j ≫ q = rankOneCellProjection G w i hi) :
    ((rankOneLiftIso G w i hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G w i hi) ≫ j) ≫ q =
        fst X.toOver (GroupActions.additiveVariety K).toOver ≫ f := by
  exact chart_project f (rankOneCellProjection G w i hi) j q hj
    (rankOneLiftIso G w i hi X f g hg).hom
    (fst X.toOver (GroupActions.additiveVariety K).toOver)
    (rankOneLiftIso_fst G w i hi X f g hg)

/-- A transported relative chart keeps the multiplication formula of its regular group lift. -/
theorem lift_rankOneLiftMap_action (l : D.toOver ⟶ (flagVariety G).toOver)
    (hj : j ≫ l = schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i))
    (Z : Over (Spec (CommRingCat.of K))) (x : Z ⟶ X.toOver)
    (y : Z ⟶ (GroupActions.additiveVariety K).toOver) :
    lift x y ≫ ((rankOneLiftIso G w i hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G w i hi) ≫ j ≫ l) =
      (x ≫ g) • (y ≫ (simpleCellIso G i).hom ≫
        schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i)) := by
  exact chart_action (lift x y) (rankOneLiftIso G w i hi X f g hg).hom
    (pullback.snd f (rankOneCellProjection G w i hi)) j l
    (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i))
    ((x ≫ g) • (y ≫ (simpleCellIso G i).hom ≫
      schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))) hj
    (lift_rankOneLiftIso_action G w i hi X f g hg Z x y)

end
end SchubertGeometry
