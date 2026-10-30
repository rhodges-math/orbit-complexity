import OrbitComplexity.GroupActions.Actions.FromPoints

/-! # Equivariance detected on rational points

Rational-point equivariance implies equivariance of the action morphisms. Smoothness
of a reduced group variety makes the scheme product reduced, so rational points determine
the morphisms in the equivariance square.

## Main results

* `GroupActions.Variety.isModHom_of_points`: rational points detect equivariance.
 -/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace GroupActions.Variety

variable {K : Type u} [Field K] [IsAlgClosed K]
  (H X Y : GroupActions.Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]

/-- A morphism equivariant on rational points is an algebraic equivariant morphism. -/
theorem isModHom_of_points (f : X.toOver ⟶ Y.toOver)
    (hsmul : ∀ (h : H.points) (x : X.points),
      mapPoints f (h • x) = h • mapPoints f x) : IsModHom H.toOver f := by
  let : Smooth H.toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec
  let P := smoothProductVariety H X
  constructor
  apply mapPoints_injective (X := P) (Y := Y)
  funext p
  apply Y.pointsEquivOverHom.injective
  change P.pointsEquivOverHom p ≫
      (ModObj.smul (M := H.toOver) (X := X.toOver) ≫ f) =
    P.pointsEquivOverHom p ≫
      ((H.toOver ◁ f) ≫ ModObj.smul (M := H.toOver) (X := Y.toOver))
  let q := P.pointsEquivOverHom p
  let h := H.pointsEquivOverHom.symm (q ≫ fst H.toOver X.toOver)
  let x := X.pointsEquivOverHom.symm (q ≫ snd H.toOver X.toOver)
  have hp : P.pointsEquivOverHom p =
      lift (H.pointsEquivOverHom h) (X.pointsEquivOverHom x) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [lift_fst, lift_snd, h, x, Equiv.apply_symm_apply, q]
  rw [hp]
  have hc := congrArg Y.pointsEquivOverHom (hsmul h x)
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • mapPoints f x) at hc
  rw [pointsEquivOverHom_smul, pointsEquivOverHom_smul] at hc
  change (lift (H.pointsEquivOverHom h) (X.pointsEquivOverHom x) ≫
      ModObj.smul (M := H.toOver) (X := X.toOver)) ≫ f =
    lift (H.pointsEquivOverHom h) (X.pointsEquivOverHom x ≫ f) ≫
      ModObj.smul (M := H.toOver) (X := Y.toOver) at hc
  simpa only [Category.assoc, lift_whiskerLeft_assoc] using hc

end GroupActions.Variety
