import OrbitComplexity.GroupActions.Actions.Points

/-! # Relative action automorphisms

A morphism from a variety to a group gives an automorphism of its product with a variety
acted on by the group. This automorphism preserves the first projection.

## Main definitions

* `GroupActions.actionTwist`: the product automorphism defined by the action.

## Main results

* `GroupActions.actionTwist_fst`: the first projection is preserved.
* `GroupActions.lift_actionTwist`: the formula on pairs of morphisms.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H X Y : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver Y.toOver]

/-- An action gives an automorphism of a product for each morphism to the group. -/
def actionTwist (b : X.toOver ⟶ H.toOver) :
    X.toOver ⊗ Y.toOver ≅ X.toOver ⊗ Y.toOver where
  hom := lift (fst X.toOver Y.toOver)
    ((fst X.toOver Y.toOver ≫ b) • snd X.toOver Y.toOver)
  inv := lift (fst X.toOver Y.toOver)
    ((fst X.toOver Y.toOver ≫ b)⁻¹ • snd X.toOver Y.toOver)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [ModObj.comp_smul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [ModObj.comp_smul]

/-- Twisting preserves the first projection of the product. -/
theorem actionTwist_fst (b : X.toOver ⟶ H.toOver) :
    (actionTwist H X Y b).hom ≫ fst X.toOver Y.toOver = fst X.toOver Y.toOver := by
  simp [actionTwist]

/-- Twisting a pair acts on its second coordinate through its first coordinate. -/
theorem lift_actionTwist (b : X.toOver ⟶ H.toOver)
    (Z : Over (Spec (CommRingCat.of K))) (x : Z ⟶ X.toOver) (y : Z ⟶ Y.toOver) :
    lift x y ≫ (actionTwist H X Y b).hom = lift x ((x ≫ b) • y) := by
  simp [actionTwist, ModObj.comp_smul]

end

end GroupActions
