import OrbitComplexity.GroupActions.Actions.FromPoints

/-! # Group morphisms detected on rational points

Multiplication identities on rational points determine the multiplication square on the
reduced product. The identity point is then preserved by cancellation.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace GroupActions.Variety

variable {K : Type u} [Field K] [IsAlgClosed K]
  (H J : GroupActions.Variety K) [GrpObj H.toOver] [GrpObj J.toOver]

/-- A variety morphism multiplicative on rational points is a group-object morphism. -/
theorem isMonHom_of_points (f : H.toOver ⟶ J.toOver)
    (hmul : ∀ x y : H.points, mapPoints f (x * y) = mapPoints f x * mapPoints f y) :
    IsMonHom f := by
  have hone : mapPoints f 1 = 1 := by
    apply mul_left_cancel (a := mapPoints f 1)
    simpa only [one_mul, mul_one] using (hmul 1 1).symm
  constructor
  · change η[H.toOver] ≫ f = η[J.toOver]
    have hc := congrArg J.pointsEquivOverHom hone
    change H.pointsEquivOverHom 1 ≫ f = J.pointsEquivOverHom 1 at hc
    rw [pointsEquivOverHom_one, pointsEquivOverHom_one] at hc
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) =
        𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
    simpa only [Hom.one_def, hu, Category.id_comp] using hc
  · let : Smooth H.toSpec :=
      TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec
    let P := smoothProductVariety H H
    apply mapPoints_injective (X := P) (Y := J)
    funext p
    apply J.pointsEquivOverHom.injective
    change P.pointsEquivOverHom p ≫ (μ[H.toOver] ≫ f) =
      P.pointsEquivOverHom p ≫ ((f ⊗ₘ f) ≫ μ[J.toOver])
    let q := P.pointsEquivOverHom p
    let x := H.pointsEquivOverHom.symm (q ≫ fst H.toOver H.toOver)
    let y := H.pointsEquivOverHom.symm (q ≫ snd H.toOver H.toOver)
    have hp : P.pointsEquivOverHom p =
        lift (H.pointsEquivOverHom x) (H.pointsEquivOverHom y) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [lift_fst, lift_snd, x, y, Equiv.apply_symm_apply, q]
    rw [hp]
    have hc := congrArg J.pointsEquivOverHom (hmul x y)
    change H.pointsEquivOverHom (x * y) ≫ f =
      J.pointsEquivOverHom (mapPoints f x * mapPoints f y) at hc
    rw [pointsEquivOverHom_mul, pointsEquivOverHom_mul] at hc
    change (lift (H.pointsEquivOverHom x) (H.pointsEquivOverHom y) ≫ μ[H.toOver]) ≫ f =
      lift (H.pointsEquivOverHom x ≫ f) (H.pointsEquivOverHom y ≫ f) ≫ μ[J.toOver] at hc
    simpa only [Category.assoc, lift_map_assoc] using hc

end GroupActions.Variety
