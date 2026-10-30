import OrbitComplexity.GroupActions.Actions.Points

/-! # Rational points in product charts for actions

A product chart whose endpoint is an action decomposes every rational endpoint into the
action of the two chart coordinates. The argument uses morphisms from the base field.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Every rational endpoint of an action product chart is the action of its two coordinates. -/
theorem exists_productChart_points (A B C H Y : GroupActions.Variety K)
    [GrpObj H.toOver] [ModObj H.toOver Y.toOver]
    (e : A.toOver ⊗ B.toOver ≅ C.toOver) (m : A.toOver ⟶ H.toOver)
    (n : B.toOver ⟶ Y.toOver) (j : C.toOver ⟶ Y.toOver)
    (he : e.hom ≫ j = (fst A.toOver B.toOver ≫ m) • (snd A.toOver B.toOver ≫ n))
    (c : C.points) : ∃ (a : A.points) (b : B.points),
      mapPoints j c = mapPoints m a • mapPoints n b := by
  let q := C.pointsEquivOverHom c ≫ e.inv
  let a := A.pointsEquivOverHom.symm (q ≫ fst A.toOver B.toOver)
  let b := B.pointsEquivOverHom.symm (q ≫ snd A.toOver B.toOver)
  refine ⟨a, b, ?_⟩
  apply Y.pointsEquivOverHom.injective
  rw [pointsEquivOverHom_smul]
  change C.pointsEquivOverHom c ≫ j =
    (A.pointsEquivOverHom a ≫ m) • (B.pointsEquivOverHom b ≫ n)
  dsimp only [a, b]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  calc
    C.pointsEquivOverHom c ≫ j = q ≫ (e.hom ≫ j) := by
      simp only [q, Category.assoc, Iso.inv_hom_id_assoc]
    _ = (q ≫ fst A.toOver B.toOver ≫ m) • (q ≫ snd A.toOver B.toOver ≫ n) := by
      rw [he, ModObj.comp_smul]

end

end GroupActions.Variety
