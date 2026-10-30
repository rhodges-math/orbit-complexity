import OrbitComplexity.FrobeniusSplitting.Cartier.HomRestriction
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionComp

/-! # Matching coefficient maps and scalar-section frames -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

/-- Matching coefficients and sections give equal restricted frame morphisms. -/
theorem localSection_composites_agree {X : Scheme.{u}} (M N : X.Modules)
    {U₀ U₁ W : X.Opens} (h₀ : W ≤ U₀) (h₁ : W ≤ U₁)
    (a₀ : M.over U₀ ⟶ (SheafOfModules.unit X.ringCatSheaf).over U₀)
    (a₁ : M.over U₁ ⟶ (SheafOfModules.unit X.ringCatSheaf).over U₁)
    (s₀ : N.val.obj (op U₀)) (s₁ : N.val.obj (op U₁))
    (c : ∀ V : Over W, Γ(X, V.left))
    (hcoef : ∀ (V : Over W) (r : M.val.obj (op V.left)),
      (show Γ(X, V.left) from
        ((a₀.val.app (op (Over.mk (V.hom ≫ homOfLE h₀))))).hom r) =
        c V * (show Γ(X, V.left) from
          ((a₁.val.app (op (Over.mk (V.hom ≫ homOfLE h₁))))).hom r))
    (hsection : ∀ V : Over W,
      (N.val.map (V.hom ≫ homOfLE h₁).op).hom s₁ =
        (N.smul (X := X) (U := V.left) (c V)).hom
          ((N.val.map (V.hom ≫ homOfLE h₀).op).hom s₀)) :
    restrictModuleHom M N h₀ (a₀ ≫ localSectionHom N U₀ s₀) =
      restrictModuleHom M N h₁ (a₁ ≫ localSectionHom N U₁ s₁) := by
  ext V r
  let O := V.unop.left
  let : Module Γ(X, O) (N.val.obj (op O)) := (N.val.obj (op O)).isModule
  let b₀ : Γ(X, O) := (a₀.val.app (op (Over.mk (V.unop.hom ≫ homOfLE h₀)))).hom r
  let b₁ : Γ(X, O) := (a₁.val.app (op (Over.mk (V.unop.hom ≫ homOfLE h₁)))).hom r
  let t₀ : N.val.obj (op O) := (N.val.map (V.unop.hom ≫ homOfLE h₀).op).hom s₀
  let t₁ : N.val.obj (op O) := (N.val.map (V.unop.hom ≫ homOfLE h₁).op).hom s₁
  have hc : b₀ = c V.unop * b₁ := hcoef V.unop r
  have ht : t₁ = (N.smul (c V.unop)).hom t₀ := hsection V.unop
  have hx : (N.smul b₀).hom t₀ = (N.smul b₁).hom t₁ := by
    have ha := congrArg (fun a : Γ(X, O) => (N.smul a).hom t₀) hc
    have hb : (N.smul (c V.unop * b₁)).hom t₀ =
        (N.smul b₁).hom ((N.smul (c V.unop)).hom t₀) :=
      (mul_smul (c V.unop) b₁ t₀).trans (smul_comm (c V.unop) b₁ t₀)
    exact ha.trans (hb.trans (congrArg (fun t : N.val.obj (op O) =>
      (N.smul b₁).hom t) ht).symm)
  have hl := (restrictModuleHom_apply M N h₀ (a₀ ≫ localSectionHom N U₀ s₀)
    V.unop r).trans (localSection_comp_apply a₀ s₀
      (Over.mk (V.unop.hom ≫ homOfLE h₀)) r)
  have hr := (restrictModuleHom_apply M N h₁ (a₁ ≫ localSectionHom N U₁ s₁)
    V.unop r).trans (localSection_comp_apply a₁ s₁
      (Over.mk (V.unop.hom ≫ homOfLE h₁)) r)
  exact hl.trans (hx.trans hr.symm)

end FrobeniusSplitting.OperatorSheaf
