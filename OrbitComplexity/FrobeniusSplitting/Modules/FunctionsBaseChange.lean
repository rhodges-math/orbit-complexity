import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Batteries.Tactic.Lint

/-! # Functions under an open Cartesian change of base -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable {P X U Y : Scheme.{u}} (p : P ⟶ U) (k : P ⟶ X)
  (j : U ⟶ Y) (q : X ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k]
  (H : IsPullback p k j q)

private def baseChangeRingIso (V : U.Opens) :
    Γ(X, q ⁻¹ᵁ j ''ᵁ V) ≅ Γ(P, p ⁻¹ᵁ V) :=
  X.presheaf.mapIso
      (eqToIso (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V)).op ≪≫
    k.appIso (p ⁻¹ᵁ V)

include H in
omit [IsOpenImmersion k] in
private theorem baseChangePreimage (V : U.Opens) :
    p ⁻¹ᵁ V ≤ k ⁻¹ᵁ (q ⁻¹ᵁ j ''ᵁ V) := by
  change p ⁻¹ᵁ V ≤ (k ≫ q) ⁻¹ᵁ j ''ᵁ V
  rw [← H.w]
  change p ⁻¹ᵁ V ≤ p ⁻¹ᵁ (j ⁻¹ᵁ j ''ᵁ V)
  rw [j.preimage_image_eq]

private theorem baseChangeRingIso_hom (V : U.Opens) :
    (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j q H V).hom =
      k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.baseChangePreimage p k j
          q H V) := by
  change X.presheaf.map (eqToHom
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V)).op ≫
    (k.appIso (p ⁻¹ᵁ V)).hom = _
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

private theorem baseChangeRingIso_scalar (V : U.Opens) :
    (j.appIso V).inv ≫ q.app (j ''ᵁ V) ≫ (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j
        q H V).hom =
      p.app V := by
  rw [FrobeniusSplitting.CharacterLine.baseChangeRingIso_hom]
  apply (cancel_epi (j.appIso V).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appIso_hom',
    Scheme.Hom.appLE_comp_appLE, H.w]

private theorem baseChangeRingIso_naturality {V W : U.Opens} (f : V ⟶ W) :
    X.presheaf.map ((Opens.map q.base).map (j.opensFunctor.map f)).op ≫
        (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j q H V).hom =
      (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j q H W).hom ≫
        P.presheaf.map ((Opens.map p.base).map f).op := by
  rw [FrobeniusSplitting.CharacterLine.baseChangeRingIso_hom,
      FrobeniusSplitting.CharacterLine.baseChangeRingIso_hom,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- An open Cartesian change of base preserves an isomorphism of structure sheaves. -/
theorem openPullback_c_isIso {A W H F : Scheme.{u}}
    (b : A ⟶ H) (a : A ⟶ W) (chart : H ⟶ F) (endpoint : W ⟶ F)
    [hchart : IsOpenImmersion chart] (hcart : IsPullback b a chart endpoint)
    [IsIso endpoint.c] : IsIso b.c := by
  have ha : IsOpenImmersion a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart hchart
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (b.app V.unop)
  rw [← @baseChangeRingIso_scalar.{u} A W H F b a chart endpoint hchart ha hcart V.unop]
  infer_instance

/-- Restricting quotient-preimage functions is the functions on the open pullback. -/
def openFunctionsBaseChange :
    (Scheme.Modules.restrictFunctor j).obj
        ((Scheme.Modules.pushforward q).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit P.ringCatSheaf) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => ?_) ?_)
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ AddCommGrpCat).mapIso
        (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j q H V.unop)) ?_
    intro (r : Γ(U, V.unop))
    ext (x : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop))
    let phi : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop) →+* Γ(P, p ⁻¹ᵁ V.unop) :=
      (FrobeniusSplitting.CharacterLine.baseChangeRingIso p k j q H V.unop).hom.hom
    let rX : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop) :=
      q.app (j ''ᵁ V.unop) ((j.appIso V.unop).inv r)
    let rP : Γ(P, p ⁻¹ᵁ V.unop) := p.app V.unop r
    change rP * phi x = phi (rX * x)
    have hs : phi rX = rP :=
      ConcreteCategory.congr_hom (FrobeniusSplitting.CharacterLine.baseChangeRingIso_scalar p k j
          q H V.unop) r
    exact ((map_mul phi rX x).trans (congrArg (fun a => a * phi x) hs)).symm
  · intro V W f
    ext x
    exact ConcreteCategory.congr_hom
      (FrobeniusSplitting.CharacterLine.baseChangeRingIso_naturality p k j q H f.unop) x

end FrobeniusSplitting.CharacterLine
