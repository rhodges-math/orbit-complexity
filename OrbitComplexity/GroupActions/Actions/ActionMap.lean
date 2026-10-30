import OrbitComplexity.GroupActions.Actions.OrbitMap

/-! # The algebraic action morphism

The unit element gives a section of the action morphism. Consequently the action morphism
is surjective on the underlying scheme, and therefore dominant.

## Main results

* `GroupActions.Variety.action_surjective`: the action morphism is scheme-surjective.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- The algebraic action morphism is surjective, with a section given by the unit element. -/
instance action_surjective :
    Surjective (ModObj.smul (M := H.toOver) (X := X.toOver)).left := by
  let s : X.toOver ⟶ H.toOver ⊗ X.toOver :=
    lift (toUnit X.toOver ≫ H.pointsEquivOverHom 1) (𝟙 X.toOver)
  have hs : s ≫ ModObj.smul (M := H.toOver) (X := X.toOver) = 𝟙 X.toOver :=
    translateMorphism_one H X
  constructor
  intro x
  refine ⟨s.left x, ?_⟩
  have hleft := congrArg Over.Hom.left hs
  exact congrArg (fun f : X.scheme ⟶ X.scheme ↦ f x) hleft

end

end GroupActions.Variety
