import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctions
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeCoefficients

/-! # Original coefficient sections in open frames -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable {P X U Y : Scheme.{u}} (p : P ⟶ U) (k : P ⟶ X)
  (j : U ⟶ Y) (q : X ⟶ Y) [IsOpenImmersion j] (h : p ≫ j = k ≫ q)

/-- Restricting a coefficient and then taking its regular frame pulls back that coefficient. -/
theorem openCoefficient_pullback (r : Γ(X, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map (FrobeniusSplitting.CharacterLine.relativeCoefficient Y
        (Over.mk q) r) ≫
        FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h =
      (Scheme.Modules.restrictUnitIso j).hom ≫
        FrobeniusSplitting.CharacterLine.relativeCoefficient U (Over.mk p) (k.appTop r) := by
  have hu : (Scheme.Modules.restrictFunctor j).map
        (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) ≫
        FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h =
      (Scheme.Modules.restrictUnitIso j).hom ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (a : Γ(Y, j ''ᵁ V.unop))
    have e : p ⁻¹ᵁ V.unop ≤ k ⁻¹ᵁ (q ⁻¹ᵁ j ''ᵁ V.unop) := by
      change p ⁻¹ᵁ V.unop ≤ (k ≫ q) ⁻¹ᵁ j ''ᵁ V.unop
      rw [← h]
      change p ⁻¹ᵁ V.unop ≤ p ⁻¹ᵁ (j ⁻¹ᵁ j ''ᵁ V.unop)
      rw [j.preimage_image_eq]
    change k.appLE (q ⁻¹ᵁ j ''ᵁ V.unop) (p ⁻¹ᵁ V.unop) e
      (q.app (j ''ᵁ V.unop) a) = p.app V.unop ((j.appIso V.unop).hom a)
    have hs : (j.appIso V.unop).inv ≫ q.app (j ''ᵁ V.unop) ≫
        k.appLE (q ⁻¹ᵁ j ''ᵁ V.unop) (p ⁻¹ᵁ V.unop) e = p.app V.unop := by
      apply (cancel_epi (j.appIso V.unop).hom).mp
      simp only [Iso.hom_inv_id_assoc]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appIso_hom',
        Scheme.Hom.appLE_comp_appLE, h]
    have hr : q.app (j ''ᵁ V.unop) ≫
        k.appLE (q ⁻¹ᵁ j ''ᵁ V.unop) (p ⁻¹ᵁ V.unop) e =
        (j.appIso V.unop).hom ≫ p.app V.unop := by
      apply (cancel_epi (j.appIso V.unop).inv).mp
      exact hs.trans (Iso.inv_hom_id_assoc (j.appIso V.unop) (p.app V.unop)).symm
    exact ConcreteCategory.congr_hom hr a
  let R := Scheme.Modules.restrictFunctor j
  let u := SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom
  let v := SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom
  let sy := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y (Over.mk q) r
  let sx := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) (k.appTop r)
  let b := FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h
  let i := (Scheme.Modules.restrictUnitIso j).hom
  change R.map (u ≫ sy) ≫ b = i ≫ v ≫ sx
  exact (congrArg (fun t => t ≫ b) (CategoryTheory.Functor.map_comp R u sy)).trans
    ((Category.assoc (R.map u) (R.map sy) b).trans
      ((congrArg (fun t => R.map u ≫ t)
          (FrobeniusSplitting.CharacterLine.openFunctionsPullback_smul p k j q h r)).trans
        ((Category.assoc (R.map u) b sx).symm.trans
          ((congrArg (fun t => t ≫ sx) hu).trans (Category.assoc i v sx)))))

/-- Over the identity base map, a coefficient section is its structure-module scalar map. -/
theorem relativeCoefficient_identity (S : Scheme.{u}) (r : Γ(S, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeCoefficient S (Over.mk (𝟙 S)) r ≫
        (Scheme.Modules.pushforwardId S).hom.app (SheafOfModules.unit S.ringCatSheaf) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit S.ringCatSheaf) r := by
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  let R := Scheme.Modules.pushforward (𝟙 S)
  let u : O ⟶ R.obj O :=
    SheafOfModules.unitToPushforwardObjUnit (𝟙 S : S ⟶ S).toRingCatSheafHom
  let e : R.obj O ⟶ O := (Scheme.Modules.pushforwardId S).hom.app O
  let t : O ⟶ O := Scheme.Modules.globalSectionsSmul O r
  have hu : u ≫ e = 𝟙 O := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (a : Γ(S, V.unop))
    exact ConcreteCategory.congr_hom (Scheme.Hom.id_app V.unop) a
  have he : R.map t ≫ e = e ≫ t := (Scheme.Modules.pushforwardId S).hom.naturality t
  change (u ≫ R.map t) ≫ e = t
  exact (Category.assoc u (R.map t) e).trans
    ((congrArg (fun q => u ≫ q) he).trans
      ((Category.assoc u e t).symm.trans
        ((congrArg (fun q => q ≫ t) hu).trans (Category.id_comp t))))

end FrobeniusSplitting.CharacterLine
