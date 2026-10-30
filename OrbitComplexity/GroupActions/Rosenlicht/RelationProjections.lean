import OrbitComplexity.GroupActions.Rosenlicht.RelationVarieties
import OrbitComplexity.GroupActions.Actions.ActionMap

/-!
# The second orbit relation projection

The second projection of the relation closure is surjective. Composing it with
the relation factorization recovers the action morphism.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The second projection from the orbit relation closure to the original variety. -/
def orbitRelationSecond : (orbitRelationVariety H X).toOver ⟶ X.toOver :=
  orbitRelationInclusion H X ≫ snd X.toOver X.toOver

/-- The second relation projection recovers the group action on the product. -/
theorem orbitRelationSecond_fac :
    orbitRelationFactor H X ≫ orbitRelationSecond H X =
      ModObj.smul (M := H.toOver) (X := X.toOver) := by
  rw [orbitRelationSecond, ← Category.assoc, orbitRelationFactor_fac,
    orbitRelationMorphism, lift_snd]

/-- The second projection of the orbit relation closure is surjective. -/
instance orbitRelationSecond_surjective : Surjective (orbitRelationSecond H X).left := by
  constructor
  intro x
  obtain ⟨t, ht⟩ := (show Function.Surjective
    (ModObj.smul (M := H.toOver) (X := X.toOver)).left from Scheme.Hom.surjective _) x
  refine ⟨(orbitRelationFactor H X).left t, ?_⟩
  have hf := congrArg
    (fun f : (productVariety H X).toOver ⟶ X.toOver ↦ f.left t)
    (orbitRelationSecond_fac H X)
  exact hf.trans ht

end

end GroupActions.Variety
