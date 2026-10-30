import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Equivariant families on a specified pullback

An action on both factors, compatible with their maps to the same target, gives
a map into their specified pullback. All compositions are checked in an arbitrary
category, before schemes or coordinate descriptions are substituted.
-/

namespace GroupActions

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [HasPullbacks C]
variable {H X Y F P : C} [MonObj H]
variable [ModObj H X] [ModObj H Y] [ModObj H F]

/-- Act on both projections of a commuting pair and lift into the same pullback. -/
noncomputable def smulPullbackLift (i : X ⟶ F) (j : Y ⟶ F)
    [IsModHom H i] [IsModHom H j]
    (t : P ⟶ H) (x : P ⟶ X) (y : P ⟶ Y) (h : x ≫ i = y ≫ j) :
    P ⟶ pullback i j :=
  pullback.lift (t • x) (t • y) (by
    rw [IsModHom.map_smul, IsModHom.map_smul, h])

/-- The first projection retains the original acted-on morphism. -/
theorem smulPullbackLift_fst (i : X ⟶ F) (j : Y ⟶ F)
    [IsModHom H i] [IsModHom H j]
    (t : P ⟶ H) (x : P ⟶ X) (y : P ⟶ Y) (h : x ≫ i = y ≫ j) :
    smulPullbackLift i j t x y h ≫ pullback.fst i j = t • x := by
  rw [smulPullbackLift, pullback.lift_fst]

/-- The second projection retains the original acted-on morphism. -/
theorem smulPullbackLift_snd (i : X ⟶ F) (j : Y ⟶ F)
    [IsModHom H i] [IsModHom H j]
    (t : P ⟶ H) (x : P ⟶ X) (y : P ⟶ Y) (h : x ≫ i = y ≫ j) :
    smulPullbackLift i j t x y h ≫ pullback.snd i j = t • y := by
  rw [smulPullbackLift, pullback.lift_snd]

end GroupActions
