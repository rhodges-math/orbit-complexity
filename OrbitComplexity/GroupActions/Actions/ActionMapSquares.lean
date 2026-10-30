import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Equivariant map squares with explicit actions

The two action structures are data arguments. Their identification is made over
arbitrary objects before applying the square to specified scheme models.
-/

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

universe u v

/-- An equivariant map carries a paired action map to the corresponding paired
action map, with both actions given explicitly. -/
theorem actionMap_chart {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {M A X D : C} [MonObj M] (a : ModObj M A) (b : ModObj M X)
    (e : A ⟶ X) (he : let := a; let := b; IsModHom M e)
    (t : D ⟶ M) (q : D ⟶ A) :
    let := a
    let := b
    (lift t q ≫ γ[M, A]) ≫ e = lift t (q ≫ e) ≫ γ[M, X] := by
  let := a
  let := b
  let := he
  exact IsModHom.map_smul e t q

end GroupActions
