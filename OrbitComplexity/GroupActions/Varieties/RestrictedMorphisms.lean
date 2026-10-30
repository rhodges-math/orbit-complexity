import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-! # Restricting variety morphisms over an open base

Restricting the target of a variety morphism to an open subset also restricts the source
to its inverse image. The resulting scheme morphism is still a morphism over the field.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- Restriction of a variety morphism to an open part of its target. -/
def restrictHom (f : X.toOver ⟶ Y.toOver) (U : Y.scheme.Opens) :
    (X.openSubvariety (f.left ⁻¹ᵁ U)).toOver ⟶ (Y.openSubvariety U).toOver := by
  refine Over.homMk (f.left ∣_ U) ?_
  change (f.left ∣_ U) ≫ (U.ι ≫ Y.toSpec) = (f.left ⁻¹ᵁ U).ι ≫ X.toSpec
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  exact congrArg (fun g ↦ (f.left ⁻¹ᵁ U).ι ≫ g)
    (show f.left ≫ Y.toSpec = X.toSpec from f.w)

/-- A dominant morphism remains dominant after restriction over an open part of the target. -/
instance restrictHom_isDominant (f : X.toOver ⟶ Y.toOver) [IsDominant f.left]
    (U : Y.scheme.Opens) : IsDominant (restrictHom f U).left :=
  IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance U

end

end GroupActions.Variety
