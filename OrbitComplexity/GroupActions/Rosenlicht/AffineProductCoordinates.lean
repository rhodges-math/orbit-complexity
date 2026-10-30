import OrbitComplexity.GroupActions.Rosenlicht.BaseFields
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Coordinates of affine products

Affine schemes over a common affine base have a product represented by the
tensor product of their global coordinate algebras. The comparison intertwines
the two projections with the two tensor-factor inclusions.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable (R : CommRingCat.{u}) (X Y : Scheme.{u})
variable [X.Over (Spec R)] [Y.Over (Spec R)] [IsAffine X] [IsAffine Y]

/-- The product of affine schemes is the spectrum of their tensor coordinate algebra. -/
def affineProductSpecIso :
    pullback (X ↘ Spec R) (Y ↘ Spec R) ≅
      Spec (.of (Γ(X, ⊤) ⊗[R] Γ(Y, ⊤))) :=
  (Over.forget (Spec R)).mapIso
    (tensorIso (X.isoSpec.asOver (Spec R)) (Y.isoSpec.asOver (Spec R))) ≪≫
      pullbackSpecIso R (Γ(X, ⊤)) (Γ(Y, ⊤))

/-- The first product projection is induced by the left tensor inclusion. -/
theorem affineProductSpecIso_fst :
    (affineProductSpecIso R X Y).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(X, ⊤) →ₐ[R]
        Γ(X, ⊤) ⊗[R] Γ(Y, ⊤)).toRingHom) =
      pullback.fst (X ↘ Spec R) (Y ↘ Spec R) ≫ X.isoSpec.hom := by
  change (((X.isoSpec.asOver (Spec R)).hom ⊗ₘ (Y.isoSpec.asOver (Spec R)).hom).left ≫
    (pullbackSpecIso R Γ(X, ⊤) Γ(Y, ⊤)).hom) ≫ _ = _
  erw [Category.assoc, pullbackSpecIso_hom_fst]
  exact Over.tensorHom_left_fst _ _ _ _

/-- The second product projection is induced by the right tensor inclusion. -/
theorem affineProductSpecIso_snd :
    (affineProductSpecIso R X Y).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[R]
        Γ(X, ⊤) ⊗[R] Γ(Y, ⊤)).toRingHom) =
      pullback.snd (X ↘ Spec R) (Y ↘ Spec R) ≫ Y.isoSpec.hom := by
  change (((X.isoSpec.asOver (Spec R)).hom ⊗ₘ (Y.isoSpec.asOver (Spec R)).hom).left ≫
    (pullbackSpecIso R Γ(X, ⊤) Γ(Y, ⊤)).hom) ≫ _ = _
  erw [Category.assoc, pullbackSpecIso_hom_snd]
  exact Over.tensorHom_left_snd _ _ _ _

end

end GroupActions
