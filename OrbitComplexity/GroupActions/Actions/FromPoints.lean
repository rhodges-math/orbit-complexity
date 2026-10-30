import OrbitComplexity.GroupActions.Actions.Points
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import TauCeti.AlgebraicGeometry.Group.Smooth

/-! # Algebraic actions from rational point actions

An algebraic product morphism agreeing with a group action on rational points satisfies the
categorical action laws. Reduced group varieties over an algebraically closed field are smooth,
so their products with varieties are reduced and rational points determine the required morphisms.

## Main definitions

* `GroupActions.Variety.modObjOfPoints`: the algebraic action from its point formula.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem existsPair (A B : GroupActions.Variety K)
    [Smooth A.toSpec]
    (z : (smoothProductVariety A B).points) :
    ∃ (a : A.points) (b : B.points),
      (smoothProductVariety A B).pointsEquivOverHom z =
        lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) := by
  let q := (smoothProductVariety A B).pointsEquivOverHom z
  let a := A.pointsEquivOverHom.symm (q ≫ fst A.toOver B.toOver)
  let b := B.pointsEquivOverHom.symm (q ≫ snd A.toOver B.toOver)
  refine ⟨a, b, ?_⟩
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [lift_fst, lift_snd, a, b, Equiv.apply_symm_apply, q]

private theorem productExt (A B Y : GroupActions.Variety K)
    [Smooth A.toSpec]
    (f g : A.toOver ⊗ B.toOver ⟶ Y.toOver)
    (h : ∀ (a : A.points) (b : B.points),
      lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) ≫ f =
        lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) ≫ g) : f = g := by
  apply mapPoints_injective (X := smoothProductVariety A B) (Y := Y)
  funext z
  apply Y.pointsEquivOverHom.injective
  change (smoothProductVariety A B).pointsEquivOverHom z ≫ f =
    (smoothProductVariety A B).pointsEquivOverHom z ≫ g
  obtain ⟨a, b, hz⟩ := existsPair A B z
  rw [hz]
  exact h a b

private theorem groupSmooth (H : GroupActions.Variety K) [GrpObj H.toOver] :
    Smooth H.toSpec :=
  TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec

attribute [local instance] groupSmooth

variable (H X : GroupActions.Variety K) [GrpObj H.toOver]
  [MulAction H.points X.points]

/-- An algebraic product morphism agreeing with a rational point action is a group action. -/
@[instance_reducible]
def modObjOfPoints (φ : H.toOver ⊗ X.toOver ⟶ X.toOver)
    (hφ : ∀ (h : H.points) (x : X.points),
      lift (H.pointsEquivOverHom h) (X.pointsEquivOverHom x) ≫ φ =
        X.pointsEquivOverHom (h • x)) : ModObj H.toOver X.toOver where
  smul := φ
  one_smul := by
    change (η ▷ X.toOver) ≫ φ = (λ_ X.toOver).hom
    have hunit : lift (toUnit X.toOver ≫ η) (𝟙 X.toOver) ≫ φ = 𝟙 X.toOver := by
      apply mapPoints_injective (X := X) (Y := X)
      funext x
      apply X.pointsEquivOverHom.injective
      change X.pointsEquivOverHom x ≫ (lift (toUnit X.toOver ≫ η) (𝟙 X.toOver) ≫ φ) =
        X.pointsEquivOverHom x ≫ 𝟙 X.toOver
      simp only [comp_lift_assoc, Category.comp_id]
      rw [← Hom.one_def, MonObj.comp_one, ← pointsEquivOverHom_one H, hφ, one_smul]
    apply (cancel_epi (λ_ X.toOver).inv).mp
    rw [Iso.inv_hom_id]
    have hl : (λ_ X.toOver).inv = lift (toUnit X.toOver) (𝟙 X.toOver) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hl, lift_whiskerRight_assoc]
    exact hunit
  mul_smul := by
    change (μ ▷ X.toOver) ≫ φ =
      (α_ H.toOver H.toOver X.toOver).hom ≫ (H.toOver ◁ φ) ≫ φ
    let P := smoothProductVariety H H
    have : Smooth P.toSpec := by
      change Smooth (Limits.pullback.fst H.toSpec H.toSpec ≫ H.toSpec)
      infer_instance
    apply productExt P X X
    intro z x
    obtain ⟨a, b, hz⟩ := existsPair H H z
    rw [hz]
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
      lift_whiskerLeft_assoc]
    rw [← Hom.mul_def, ← pointsEquivOverHom_mul H, hφ, hφ, hφ, mul_smul]

end

end GroupActions.Variety
