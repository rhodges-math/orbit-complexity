import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group structures induced through monomorphisms

Group operations that factor through a monomorphism satisfy the group laws by cancellation.

## Main definitions

* `GroupActions.grpObjOfMono`: group structure induced through a monomorphism.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace GroupActions

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {H U : C} [GrpObj H]

/-- Group operations inherited through a monomorphism form a group object. -/
@[instance_reducible]
def grpObjOfMono (i : U ⟶ H) [Mono i]
    (one : 𝟙_ C ⟶ U) (mul : U ⊗ U ⟶ U) (inv : U ⟶ U)
    (h_one : one ≫ i = η[H]) (h_mul : mul ≫ i = (i ⊗ₘ i) ≫ μ[H])
    (h_inv : inv ≫ i = i ≫ ι[H]) : GrpObj U where
  one := one
  mul := mul
  inv := inv
  one_mul := by
    apply (cancel_mono i).mp
    rw [Category.assoc, h_mul]
    have h : (one ▷ U) ≫ (i ⊗ₘ i) =
        lift (toUnit _ ≫ η[H]) (snd _ _ ≫ i) := by
      ext <;> simp [h_one]
      congr 1
      exact toUnit_unique _ _
    rw [← Category.assoc, h, MonObj.lift_comp_one_left, leftUnitor_hom]
  mul_one := by
    apply (cancel_mono i).mp
    rw [Category.assoc, h_mul]
    have h : (U ◁ one) ≫ (i ⊗ₘ i) =
        lift (fst _ _ ≫ i) (toUnit _ ≫ η[H]) := by
      ext <;> simp [h_one]
      congr 1
      exact toUnit_unique _ _
    rw [← Category.assoc, h, MonObj.lift_comp_one_right, rightUnitor_hom]
  mul_assoc := by
    apply (cancel_mono i).mp
    have h1 : (mul ▷ U) ≫ (i ⊗ₘ i) =
        ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[H] ▷ H) := by
      ext
      · simp only [Category.assoc, tensorHom_fst, whiskerRight_fst]
        rw [whiskerRight_fst_assoc, tensorHom_fst_assoc, h_mul]
      · simp only [Category.assoc, tensorHom_snd, whiskerRight_snd,
          whiskerRight_snd_assoc]
    have h2 : (U ◁ mul) ≫ (i ⊗ₘ i) =
        (i ⊗ₘ (i ⊗ₘ i)) ≫ (H ◁ μ[H]) := by
      ext
      · simp only [Category.assoc, tensorHom_fst, whiskerLeft_fst,
          whiskerLeft_fst_assoc]
      · simp only [Category.assoc, tensorHom_snd, whiskerLeft_snd]
        rw [whiskerLeft_snd_assoc, tensorHom_snd_assoc, h_mul]
    simp only [Category.assoc, h_mul]
    rw [← Category.assoc, h1, Category.assoc, MonObj.mul_assoc]
    rw [associator_naturality_assoc]
    rw [← Category.assoc (U ◁ mul), h2]
    simp only [Category.assoc]
  left_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, h_mul, lift_map_assoc, h_inv,
      Category.id_comp, h_one]
    exact GrpObj.lift_comp_inv_left i
  right_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, h_mul, lift_map_assoc, h_inv,
      Category.id_comp, h_one]
    exact GrpObj.lift_comp_inv_right i

end GroupActions
