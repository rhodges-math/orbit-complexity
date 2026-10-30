import OrbitComplexity.SchubertGeometry.Deodhar.BaseChange
import OrbitComplexity.SchubertGeometry.Deodhar.LiftTwist

/-! # Relative simple-extension cell charts

Changing a regular flag lift modifies the additive coordinate by its Borel comparison factor.
The resulting chart is an isomorphism onto the pullback of the increasing-cell projection.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X : GroupActions.Variety K)
  (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)

/-- A regular group lift determines an additive chart on the pulled-back cell projection. -/
def rankOneLiftIso : X.toOver ⊗ (GroupActions.additiveVariety K).toOver ≅
    pullback f (rankOneCellProjection G w i hw) :=
  rankOneLiftTwist G w i X f g hg ≪≫ rankOneCellPullbackIso G w i hw X.toOver f

private theorem trans_project {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (j : B ≅ D) (p : D ⟶ E) (m : B ⟶ E) (h : j.hom ≫ p = m) :
    (e ≪≫ j).hom ≫ p = e.hom ≫ m := by
  rw [Iso.trans_hom, Category.assoc, h]

private theorem liftIso_hom : (rankOneLiftIso G w i hw X f g hg).hom =
    (rankOneLiftTwist G w i X f g hg).hom ≫
      (rankOneCellPullbackIso G w i hw X.toOver f).hom := rfl

/-- The relative additive chart preserves its base point. -/
theorem rankOneLiftIso_fst : (rankOneLiftIso G w i hw X f g hg).hom ≫
    pullback.fst f (rankOneCellProjection G w i hw) =
      fst X.toOver (GroupActions.additiveVariety K).toOver := by
  rw [liftIso_hom, Category.assoc, rankOneCellPullbackIso_fst, rankOneLiftTwist_fst]

/-- The extension point is the canonical product chart after the Borel coordinate change. -/
theorem rankOneLiftIso_snd : (rankOneLiftIso G w i hw X f g hg).hom ≫
    pullback.snd f (rankOneCellProjection G w i hw) =
      (rankOneLiftTwist G w i X f g hg).hom ≫
        ((f ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver) ≫
          (rankOneCellProductIso G w i hw).hom) := by
  exact trans_project (rankOneLiftTwist G w i X f g hg)
    (rankOneCellPullbackIso G w i hw X.toOver f)
    (pullback.snd f (rankOneCellProjection G w i hw)) _
    (rankOneCellPullbackIso_snd G w i hw X.toOver f)

end
end SchubertGeometry
