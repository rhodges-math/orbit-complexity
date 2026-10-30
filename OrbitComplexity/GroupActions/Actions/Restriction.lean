import OrbitComplexity.GroupActions.Actions.Points

/-! # Restriction of algebraic actions

Morphisms of algebraic groups induce homomorphisms on rational points. Mathlib's restriction
of a module object along a monoid morphism gives the corresponding restricted point action.

## Main definitions

* `GroupActions.Variety.mapPointsHom`: the homomorphism on rational points of a group morphism.

## Main results

* `GroupActions.Variety.restricted_smul`: restricted algebraic actions induce restricted point
  actions.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {H G : GroupActions.Variety K} [GrpObj H.toOver]
  [GrpObj G.toOver]

/-- A morphism of group varieties induces a homomorphism of rational-point groups. -/
def mapPointsHom (f : H.toOver ⟶ G.toOver) [IsMonHom f] : H.points →* G.points where
  toFun := mapPoints f
  map_one' := by
    apply G.pointsEquivOverHom.injective
    change H.pointsEquivOverHom 1 ≫ f = G.pointsEquivOverHom 1
    rw [pointsEquivOverHom_one, pointsEquivOverHom_one, MonObj.one_comp]
  map_mul' h k := by
    apply G.pointsEquivOverHom.injective
    change H.pointsEquivOverHom (h * k) ≫ f =
      G.pointsEquivOverHom (mapPoints f h) * G.pointsEquivOverHom (mapPoints f k)
    rw [pointsEquivOverHom_mul, MonObj.mul_comp]
    rfl

/-- Restriction of an algebraic action agrees with restriction on rational points. -/
theorem restricted_smul (f : H.toOver ⟶ G.toOver) [IsMonHom f]
    (X : GroupActions.Variety K) [ModObj G.toOver X.toOver] (h : H.points) (x : X.points) :
    letI := Mod.scalarRestriction f X.toOver
    h • x = mapPoints f h • x := by
  let := Mod.scalarRestriction f X.toOver
  apply X.pointsEquivOverHom.injective
  rw [pointsEquivOverHom_smul, pointsEquivOverHom_smul]
  simp only [CategoryTheory.Hom.smul_def]
  change lift (H.pointsEquivOverHom h) (X.pointsEquivOverHom x) ≫
      ((f ▷ X.toOver) ≫ ModObj.smul (M := G.toOver) (X := X.toOver)) =
    lift (H.pointsEquivOverHom h ≫ f) (X.pointsEquivOverHom x) ≫
      ModObj.smul (M := G.toOver) (X := X.toOver)
  rw [← Category.assoc, lift_whiskerRight]

end

end GroupActions.Variety
