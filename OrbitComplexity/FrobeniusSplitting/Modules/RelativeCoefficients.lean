import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars

/-! # Relative module sections from original regular coefficients -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable (S : Scheme.{u})

/-- An original global regular function gives its module section over the same base. -/
def relativeCoefficient (X : Over S) (r : Γ(X.left, ⊤)) :
    SheafOfModules.unit S.ringCatSheaf ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X
        :=
  SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom ≫
    FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X r

/-- On every open the section multiplies by the restriction of the original coefficient. -/
theorem relativeCoefficient_app (X : Over S) (r : Γ(X.left, ⊤)) (V : S.Opens)
    (a : Γ(S, V)) :
    ((FrobeniusSplitting.CharacterLine.relativeCoefficient S X r).val.app (.op V)).hom a =
      X.left.presheaf.map (X.hom ⁻¹ᵁ V).leTop.op r * X.hom.app V a := rfl

private theorem app_comp_over {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) (V : Z.Opens)
    (e : h ⁻¹ᵁ V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ V)) :
    g.app V ≫ f.appLE (g ⁻¹ᵁ V) (h ⁻¹ᵁ V) e = h.app V := by
  subst h
  exact congrArg (fun t => g.app V ≫ t) (Scheme.Hom.appLE_eq_app f)

private theorem unit_pullback {X Y : Over S} (f : X ⟶ Y) :
    SheafOfModules.unitToPushforwardObjUnit Y.hom.toRingCatSheafHom ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f =
      SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (a : Γ(S, V.unop))
  have e : X.hom ⁻¹ᵁ V.unop ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ V.unop) := by
    change X.hom ⁻¹ᵁ V.unop ≤ (f.left ≫ Y.hom) ⁻¹ᵁ V.unop
    rw [f.w]
  change f.left.appLE (Y.hom ⁻¹ᵁ V.unop) (X.hom ⁻¹ᵁ V.unop) e
    (Y.hom.app V.unop a) = X.hom.app V.unop a
  have h : Y.hom.app V.unop ≫
      f.left.appLE (Y.hom ⁻¹ᵁ V.unop) (X.hom ⁻¹ᵁ V.unop) e =
      X.hom.app V.unop := FrobeniusSplitting.CharacterLine.app_comp_over f.left Y.hom X.hom f.w
          V.unop e
  exact ConcreteCategory.congr_hom h a

/-- Relative pullback retains the original coefficient pulled back by the scheme morphism. -/
theorem relativeCoefficient_pullback {X Y : Over S} (f : X ⟶ Y) (r : Γ(Y.left, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeCoefficient S Y r ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f =
      FrobeniusSplitting.CharacterLine.relativeCoefficient S X (f.left.appTop r) := by
  unfold FrobeniusSplitting.CharacterLine.relativeCoefficient
  let u := SheafOfModules.unitToPushforwardObjUnit Y.hom.toRingCatSheafHom
  let R := FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f
  let sy := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Y r
  let sx := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (f.left.appTop r)
  exact (Category.assoc u sy R).trans
    ((congrArg (fun t => u ≫ t) (FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul S f
        r)).trans
      ((Category.assoc u R sx).symm.trans
        (congrArg (fun t => t ≫ sx) (FrobeniusSplitting.CharacterLine.unit_pullback S f))))

/-- Multiplying a relative coefficient section multiplies its original global function. -/
theorem relativeCoefficient_multiply (X : Over S) (r s : Γ(X.left, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeCoefficient S X r ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X s =
      FrobeniusSplitting.CharacterLine.relativeCoefficient S X (r * s) := by
  unfold FrobeniusSplitting.CharacterLine.relativeCoefficient
  let u := SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom
  let sr := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X r
  let ss := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X s
  have hs : sr ≫ ss = FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (r * s) :=
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul_mul S X s r).symm.trans
      (congrArg (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X) (mul_comm s r))
  exact (Category.assoc u sr ss).trans (congrArg (fun t => u ≫ t) hs)

/-- A regular character equation lifts the same coefficient section through its equalizer. -/
theorem relativeCoefficient_character {X Q : Over S} (m f : Q ⟶ X)
    (r : Γ(X.left, ⊤)) (v : Γ(Q.left, ⊤))
    (h : m.left.appTop r = f.left.appTop r * v) :
    FrobeniusSplitting.CharacterLine.relativeCoefficient S X r ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S m =
      FrobeniusSplitting.CharacterLine.relativeCoefficient S X r ≫
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) := by
  calc
    _ = FrobeniusSplitting.CharacterLine.relativeCoefficient S Q (m.left.appTop r) :=
        FrobeniusSplitting.CharacterLine.relativeCoefficient_pullback S m r
    _ = FrobeniusSplitting.CharacterLine.relativeCoefficient S Q (f.left.appTop r * v) :=
      congrArg (FrobeniusSplitting.CharacterLine.relativeCoefficient S Q) h
    _ = FrobeniusSplitting.CharacterLine.relativeCoefficient S Q (f.left.appTop r) ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v :=
      (FrobeniusSplitting.CharacterLine.relativeCoefficient_multiply S Q (f.left.appTop r) v).symm
    _ = (FrobeniusSplitting.CharacterLine.relativeCoefficient S X r ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f) ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v :=
      congrArg (fun t => t ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v)
        (FrobeniusSplitting.CharacterLine.relativeCoefficient_pullback S f r).symm
    _ = _ := Category.assoc _ _ _

end FrobeniusSplitting.CharacterLine
