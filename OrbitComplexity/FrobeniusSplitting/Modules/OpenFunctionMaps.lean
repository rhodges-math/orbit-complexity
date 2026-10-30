import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctions

/-! # Naturality of regular functions in an open square -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

private theorem appLE_eq_of_hom_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (W : Y.Opens) (V : X.Opens) (ef : V ≤ f ⁻¹ᵁ W) (eg : V ≤ g ⁻¹ᵁ W) :
    f.appLE W V ef = g.appLE W V eg := by
  subst g
  rfl

variable {U Y P₁ P₂ X₁ X₂ : Scheme.{u}}
  (j : U ⟶ Y) [IsOpenImmersion j]
  (p₁ : P₁ ⟶ U) (p₂ : P₂ ⟶ U) (q₁ : X₁ ⟶ Y) (q₂ : X₂ ⟶ Y)
  (k₁ : P₁ ⟶ X₁) (k₂ : P₂ ⟶ X₂)
  (h₁ : p₁ ≫ j = k₁ ≫ q₁) (h₂ : p₂ ≫ j = k₂ ≫ q₂)

/-- A map between the original regular squares preserves pullback on every open. -/
theorem openFunctionsPullback_natural
    (M : Over.mk q₁ ⟶ Over.mk q₂) (N : Over.mk p₁ ⟶ Over.mk p₂)
    (hk : N.left ≫ k₂ = k₁ ≫ M.left) :
    (Scheme.Modules.restrictFunctor j).map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap
        Y M) ≫
        FrobeniusSplitting.CharacterLine.openFunctionsPullback p₁ k₁ j q₁ h₁ =
      FrobeniusSplitting.CharacterLine.openFunctionsPullback p₂ k₂ j q₂ h₂ ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap U N := by
  ext V s
  change Γ(X₂, q₂ ⁻¹ᵁ j ''ᵁ V) at s
  have wM : M.left ≫ q₂ = q₁ := M.w
  have wN : N.left ≫ p₂ = p₁ := N.w
  have eM : q₁ ⁻¹ᵁ j ''ᵁ V ≤ M.left ⁻¹ᵁ (q₂ ⁻¹ᵁ j ''ᵁ V) := by
    change q₁ ⁻¹ᵁ j ''ᵁ V ≤ (M.left ≫ q₂) ⁻¹ᵁ j ''ᵁ V
    rw [wM]
  have eN : p₁ ⁻¹ᵁ V ≤ N.left ⁻¹ᵁ (p₂ ⁻¹ᵁ V) := by
    change p₁ ⁻¹ᵁ V ≤ (N.left ≫ p₂) ⁻¹ᵁ V
    rw [wN]
  have e₁ : p₁ ⁻¹ᵁ V ≤ k₁ ⁻¹ᵁ (q₁ ⁻¹ᵁ j ''ᵁ V) := by
    change p₁ ⁻¹ᵁ V ≤ (k₁ ≫ q₁) ⁻¹ᵁ j ''ᵁ V
    rw [← h₁]
    change p₁ ⁻¹ᵁ V ≤ p₁ ⁻¹ᵁ (j ⁻¹ᵁ j ''ᵁ V)
    rw [j.preimage_image_eq]
  have e₂ : p₂ ⁻¹ᵁ V ≤ k₂ ⁻¹ᵁ (q₂ ⁻¹ᵁ j ''ᵁ V) := by
    change p₂ ⁻¹ᵁ V ≤ (k₂ ≫ q₂) ⁻¹ᵁ j ''ᵁ V
    rw [← h₂]
    change p₂ ⁻¹ᵁ V ≤ p₂ ⁻¹ᵁ (j ⁻¹ᵁ j ''ᵁ V)
    rw [j.preimage_image_eq]
  change k₁.appLE (q₁ ⁻¹ᵁ j ''ᵁ V) (p₁ ⁻¹ᵁ V) e₁
      (M.left.appLE (q₂ ⁻¹ᵁ j ''ᵁ V) (q₁ ⁻¹ᵁ j ''ᵁ V) eM s) =
    N.left.appLE (p₂ ⁻¹ᵁ V) (p₁ ⁻¹ᵁ V) eN
      (k₂.appLE (q₂ ⁻¹ᵁ j ''ᵁ V) (p₂ ⁻¹ᵁ V) e₂ s)
  have hr : M.left.appLE (q₂ ⁻¹ᵁ j ''ᵁ V) (q₁ ⁻¹ᵁ j ''ᵁ V) eM ≫
        k₁.appLE (q₁ ⁻¹ᵁ j ''ᵁ V) (p₁ ⁻¹ᵁ V) e₁ =
      k₂.appLE (q₂ ⁻¹ᵁ j ''ᵁ V) (p₂ ⁻¹ᵁ V) e₂ ≫
        N.left.appLE (p₂ ⁻¹ᵁ V) (p₁ ⁻¹ᵁ V) eN :=
    (Scheme.Hom.appLE_comp_appLE k₁ M.left
      (q₂ ⁻¹ᵁ j ''ᵁ V) (q₁ ⁻¹ᵁ j ''ᵁ V) (p₁ ⁻¹ᵁ V) eM e₁).trans
      ((FrobeniusSplitting.CharacterLine.appLE_eq_of_hom_eq hk.symm (q₂ ⁻¹ᵁ j ''ᵁ V) (p₁ ⁻¹ᵁ V) _
          _).trans
        (Scheme.Hom.appLE_comp_appLE N.left k₂
          (q₂ ⁻¹ᵁ j ''ᵁ V) (p₂ ⁻¹ᵁ V) (p₁ ⁻¹ᵁ V) e₂ eN).symm)
  exact ConcreteCategory.congr_hom hr s

end FrobeniusSplitting.CharacterLine
