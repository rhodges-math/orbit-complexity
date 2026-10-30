import OrbitComplexity.GroupActions.Rosenlicht.ProductSections
import OrbitComplexity.GroupActions.Actions.OrbitMap

/-! # Algebraic action families -/

noncomputable section
namespace GroupActions.Variety
open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem action_section (A B H X P : GroupActions.Variety K)
    [IrreducibleSpace A.scheme] [IrreducibleSpace P.scheme]
    [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    (f : A.toOver ⟶ B.toOver) (j : B.toOver ⟶ H.toOver)
    (e : X.toOver ≅ P.toOver) (a : A.points) :
    pointSection A P a ≫ (f ⊗ₘ e.inv) ≫ (j ▷ X.toOver) ≫
        ModObj.smul (M := H.toOver) (X := X.toOver) ≫ e.hom =
      e.inv ≫ translateMorphism H X (mapPoints (f ≫ j) a) ≫ e.hom := by
  have hp : H.pointsEquivOverHom (mapPoints (f ≫ j) a) =
      A.pointsEquivOverHom a ≫ f ≫ j := by
    apply Over.OverMorphism.ext
    rfl
  simp only [pointSection, translateMorphism, CategoryTheory.Hom.smul_def,
    lift_map_assoc, lift_whiskerRight_assoc, comp_lift_assoc, hp,
    Category.id_comp, Category.comp_id, Category.assoc, comp_toUnit_assoc]

end GroupActions.Variety
end

noncomputable section
namespace GroupActions.Variety
open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem eq_of_pointSections (A X Y : GroupActions.Variety K)
    [IrreducibleSpace A.scheme] [IrreducibleSpace X.scheme]
    (f g : A.toOver ⊗ X.toOver ⟶ Y.toOver)
    (h : ∀ a : A.points, pointSection A X a ≫ f = pointSection A X a ≫ g) : f = g := by
  let P := productVariety A X
  apply mapPoints_injective (X := P) (Y := Y)
  funext p
  apply Y.pointsEquivOverHom.injective
  let q := P.pointsEquivOverHom p
  let a := A.pointsEquivOverHom.symm (q ≫ fst A.toOver X.toOver)
  let x := X.pointsEquivOverHom.symm (q ≫ snd A.toOver X.toOver)
  have hu : X.pointsEquivOverHom x ≫ toUnit X.toOver =
      𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  have hp : q = X.pointsEquivOverHom x ≫ pointSection A X a := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, pointSection, lift_fst, ← Category.assoc, hu, Category.id_comp]
      exact (A.pointsEquivOverHom.apply_symm_apply _).symm
    · rw [Category.assoc, pointSection, lift_snd, Category.comp_id]
      exact (X.pointsEquivOverHom.apply_symm_apply _).symm
  change q ≫ f = q ≫ g
  rw [hp, Category.assoc, h, Category.assoc]

end GroupActions.Variety
end

noncomputable section
namespace GroupActions.Variety
open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Rational sections determine a family obtained by transporting an algebraic action. -/
theorem actionFamily_eq_of_sections (A B H X P : GroupActions.Variety K)
    [IrreducibleSpace A.scheme] [IrreducibleSpace P.scheme]
    [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    (f : A.toOver ⟶ B.toOver) (j : B.toOver ⟶ H.toOver)
    (e : X.toOver ≅ P.toOver) (F : A.toOver ⊗ P.toOver ⟶ P.toOver)
    (h : ∀ a : A.points,
      e.inv ≫ translateMorphism H X (mapPoints (f ≫ j) a) ≫ e.hom =
        pointSection A P a ≫ F) :
    (f ⊗ₘ e.inv) ≫ (j ▷ X.toOver) ≫ ModObj.smul (M := H.toOver) (X := X.toOver) ≫
      e.hom = F := by
  apply eq_of_pointSections A P P
  intro a
  exact (action_section A B H X P f j e a).trans (h a)

end GroupActions.Variety
end
