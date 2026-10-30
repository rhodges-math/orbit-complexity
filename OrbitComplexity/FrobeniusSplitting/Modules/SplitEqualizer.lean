import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # The equalizer determined by an identity section -/

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u v

namespace FrobeniusSplitting.CharacterLine

variable {C : Type u} [Category.{v} C] {A B D : C}

/-- A splitting pulled back along the identity insertion trivializes the equalizer. -/
def splitEqualizerIso (a g : B ⟶ D) [HasEqualizer a g]
    (t : D ⟶ B) (r : B ⟶ A) (b : A ⟶ B)
    (ha : a ≫ t = 𝟙 B) (hg : g ≫ t = r ≫ b)
    (hr : b ≫ r = 𝟙 A) (hb : b ≫ a = b ≫ g) :
    A ≅ equalizer a g where
  hom := equalizer.lift b hb
  inv := equalizer.ι a g ≫ r
  hom_inv_id := by rw [← Category.assoc, equalizer.lift_ι, hr]
  inv_hom_id := by
    apply (cancel_mono (equalizer.ι a g)).mp
    simp only [Category.assoc, equalizer.lift_ι, Category.id_comp]
    calc
      equalizer.ι a g ≫ r ≫ b = equalizer.ι a g ≫ g ≫ t := by rw [hg]
      _ = equalizer.ι a g ≫ a ≫ t := by rw [← equalizer.condition_assoc]
      _ = equalizer.ι a g := by rw [ha, Category.comp_id]

end FrobeniusSplitting.CharacterLine
