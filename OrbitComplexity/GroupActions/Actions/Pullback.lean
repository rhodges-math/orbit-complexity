import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Actions on equivariant pullbacks

Two equivariant morphisms give an action on their pullback. Its action morphism is
the pullback lift of the two component actions, and both projections are equivariant.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (H : C) [MonObj H] {X Y Z : C}
  [ModObj H X] [ModObj H Y] [ModObj H Z]
  (f : X ⟶ Z) (g : Y ⟶ Z) [IsModHom H f] [IsModHom H g]
  [HasPullback f g]

private def pullbackSmul : H ⊗ pullback f g ⟶ pullback f g :=
  pullback.lift
    ((H ◁ pullback.fst f g) ≫ γ[H, X])
    ((H ◁ pullback.snd f g) ≫ γ[H, Y])
    (by
      simp only [Category.assoc, IsModHom.smul_hom]
      change (H ◁ pullback.fst f g) ≫ (H ◁ f) ≫ γ[H, Z] =
        (H ◁ pullback.snd f g) ≫ (H ◁ g) ≫ γ[H, Z]
      rw [← whiskerLeft_comp_assoc, pullback.condition, whiskerLeft_comp_assoc])

private theorem pullbackSmul_fst :
    pullbackSmul H f g ≫ pullback.fst f g = (H ◁ pullback.fst f g) ≫ γ[H, X] := by
  simp only [pullbackSmul, pullback.lift_fst]

private theorem pullbackSmul_snd :
    pullbackSmul H f g ≫ pullback.snd f g = (H ◁ pullback.snd f g) ≫ γ[H, Y] := by
  simp only [pullbackSmul, pullback.lift_snd]

private theorem unit_comp {P A : C} [ModObj H A]
    (a : H ⊗ P ⟶ P) (p : P ⟶ A) (h : a ≫ p = (H ◁ p) ≫ γ[H, A]) :
    (η[H] ▷ P) ≫ a ≫ p = (λ_ P).hom ≫ p := by
  rw [h, ← whisker_exchange_assoc, ModObj.one_smul_self, leftUnitor_naturality]

private theorem mul_comp {P A : C} [ModObj H A]
    (a : H ⊗ P ⟶ P) (p : P ⟶ A) (h : a ≫ p = (H ◁ p) ≫ γ[H, A]) :
    (μ[H] ▷ P) ≫ a ≫ p = (α_ H H P).hom ≫ (H ◁ a) ≫ a ≫ p := by
  calc
    (μ[H] ▷ P) ≫ a ≫ p = ((H ⊗ H) ◁ p) ≫ (μ[H] ▷ A) ≫ γ[H, A] := by
      rw [h, ← whisker_exchange_assoc]
    _ = (α_ H H P).hom ≫ (H ◁ H ◁ p) ≫ (H ◁ γ[H, A]) ≫ γ[H, A] := by
      rw [ModObj.mul_smul_self, associator_naturality_right_assoc]
    _ = (α_ H H P).hom ≫ (H ◁ a) ≫ a ≫ p := by
      symm
      rw [h, ← whiskerLeft_comp_assoc, h, whiskerLeft_comp_assoc]

/-- Equivariant morphisms induce an action on their pullback. -/
@[instance_reducible] def pullbackAction : ModObj H (pullback f g) where
  smul := pullbackSmul H f g
  one_smul := by
    change (η[H] ▷ pullback f g) ≫ pullbackSmul H f g = (λ_ (pullback f g)).hom
    apply pullback.hom_ext
    · simpa only [Category.assoc] using
        unit_comp H (pullbackSmul H f g) (pullback.fst f g) (pullbackSmul_fst H f g)
    · simpa only [Category.assoc] using
        unit_comp H (pullbackSmul H f g) (pullback.snd f g) (pullbackSmul_snd H f g)
  mul_smul := by
    change (μ[H] ▷ pullback f g) ≫ pullbackSmul H f g =
      (α_ H H (pullback f g)).hom ≫ (H ◁ pullbackSmul H f g) ≫ pullbackSmul H f g
    apply pullback.hom_ext
    · simpa only [Category.assoc] using
        mul_comp H (pullbackSmul H f g) (pullback.fst f g) (pullbackSmul_fst H f g)
    · simpa only [Category.assoc] using
        mul_comp H (pullbackSmul H f g) (pullback.snd f g) (pullbackSmul_snd H f g)

/-- The first projection of the pullback action is equivariant. -/
theorem pullbackAction_fst :
    letI := pullbackAction H f g
    IsModHom H (pullback.fst f g) := by
  let := pullbackAction H f g
  exact ⟨pullbackSmul_fst H f g⟩

/-- The second projection of the pullback action is equivariant. -/
theorem pullbackAction_snd :
    letI := pullbackAction H f g
    IsModHom H (pullback.snd f g) := by
  let := pullbackAction H f g
  exact ⟨pullbackSmul_snd H f g⟩

end

end GroupActions
