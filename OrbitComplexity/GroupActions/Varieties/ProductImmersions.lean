import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Immersions in products over a scheme

Products preserve open immersions. A section of the first projection is closed when the
second factor is separated over the base.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace GroupActions
noncomputable section
universe u
variable {S : Scheme.{u}}

/-- The product over a scheme of two open immersions is an open immersion. -/
instance tensorHom_isOpen {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ⊗ₘ g).left := by
  change IsOpenImmersion (pullback.map X.hom Y.hom X'.hom Y'.hom
    f.left g.left (𝟙 S) (by simpa only [Category.comp_id] using f.w.symm)
      (by simpa only [Category.comp_id] using g.w.symm))
  infer_instance

/-- A section into a product is closed when its second factor is separated over the base. -/
theorem tensorSection_isClosed (X Y : Over S) [IsSeparated Y.hom] (y : X ⟶ Y) :
    IsClosedImmersion (lift (𝟙 X) y).left := by
  have hs : (lift (𝟙 X) y).left ≫ (fst X Y).left = 𝟙 X.left :=
    congrArg (fun f : X ⟶ X => f.left) (lift_fst (𝟙 X) y)
  have : IsSeparated (fst X Y).left := by
    change IsSeparated (pullback.fst X.hom Y.hom)
    infer_instance
  have : IsClosedImmersion ((lift (𝟙 X) y).left ≫ (fst X Y).left) := by
    rw [hs]
    infer_instance
  exact IsClosedImmersion.of_comp (lift (𝟙 X) y).left (fst X Y).left

end
end GroupActions
