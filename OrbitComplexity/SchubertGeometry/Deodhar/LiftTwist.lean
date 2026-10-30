import OrbitComplexity.SchubertGeometry.Deodhar.CellLifts
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Actions.RelativeTwist

/-! # Changes of additive coordinates between flag lifts

The Borel action on the simple cell changes the additive coordinate when the regular
group-valued lift of the preceding flag is changed. This gives an automorphism over the base.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (X : GroupActions.Variety K)
  (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)

/-- The Borel comparison factor gives a relative change of the simple-cell additive coordinate. -/
def rankOneLiftTwist : X.toOver ⊗ (GroupActions.additiveVariety K).toOver ≅
    X.toOver ⊗ (GroupActions.additiveVariety K).toOver :=
  (tensorIso (Iso.refl X.toOver) (simpleCellIso G i) ≪≫
    GroupActions.actionTwist (GroupActions.borelVariety G) X
      (schubertCell G (RootPairing.weylGroup.ofIdx G.rootSystem i))
      (schubertBorelLift G w X f g hg)) ≪≫
    tensorIso (Iso.refl X.toOver) (simpleCellIso G i).symm

private theorem liftTwist_hom : (rankOneLiftTwist G w i X f g hg).hom =
    ((𝟙 X.toOver ⊗ₘ (simpleCellIso G i).hom) ≫
      (GroupActions.actionTwist (GroupActions.borelVariety G) X
        (schubertCell G (RootPairing.weylGroup.ofIdx G.rootSystem i))
        (schubertBorelLift G w X f g hg)).hom) ≫
      (𝟙 X.toOver ⊗ₘ (simpleCellIso G i).inv) := rfl

/-- Changing the additive coordinate preserves its base point. -/
theorem rankOneLiftTwist_fst : (rankOneLiftTwist G w i X f g hg).hom ≫
    fst X.toOver (GroupActions.additiveVariety K).toOver =
      fst X.toOver (GroupActions.additiveVariety K).toOver := by
  rw [liftTwist_hom, Category.assoc, tensorHom_fst, Category.comp_id,
    Category.assoc, GroupActions.actionTwist_fst, tensorHom_fst, Category.comp_id]

/-- The relative coordinate change acts through the Borel factor on the simple Schubert cell. -/
theorem lift_rankOneLiftTwist (Z : Over (Spec (CommRingCat.of K)))
    (x : Z ⟶ X.toOver) (y : Z ⟶ (GroupActions.additiveVariety K).toOver) :
    lift x y ≫ (rankOneLiftTwist G w i X f g hg).hom =
      lift x (((x ≫ schubertBorelLift G w X f g hg) •
        (y ≫ (simpleCellIso G i).hom)) ≫ (simpleCellIso G i).inv) := by
  rw [liftTwist_hom, ← Category.assoc, ← Category.assoc, lift_map, Category.comp_id,
    GroupActions.lift_actionTwist, lift_map, Category.comp_id]

end
end SchubertGeometry
