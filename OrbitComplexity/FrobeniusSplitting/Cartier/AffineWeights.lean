import OrbitComplexity.FrobeniusSplitting.Cartier.AffineOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorCharts

/-! # Affine trace weights on open subschemes -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

private abbrev affine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))
private def base (C : Type u) [CommRing C] : affine C ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : C →+* Polynomial C))
private def trace (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p] :=
  (univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p)

/-- On each affine-line open, weights parametrize all Frobenius-linear sheaf operators. -/
theorem affineTrace_weight_open_bijective (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] [PerfectRing C p] (U : (affine C).Opens) :
    Function.Bijective (fun r : Γ(affine C, U) =>
      ((trace C p).restrict U).inputWeight (U.topIso.inv r)) := by
  have hc : IsIso ((affineTraceFrame C p).val.app (op U)) :=
    ((SheafOfModules.evaluation (affine C).ringCatSheaf (op U)).mapIso
      (@asIso _ _ _ _ (affineTraceFrame C p) (affineTraceFrame_isIso C p))).isIso_hom
  have hb := (ConcreteCategory.isIso_iff_bijective
    ((affineTraceFrame C p).val.app (op U))).mp hc
  have hf : Function.Bijective (fun r : Γ(affine C, U) =>
      openOperatorEquiv C p (base C) U
        (operatorModuleSections (sheafFrobenius C p (base C)) U
          (((affineTraceFrame C p).val.app (op U)).hom r))) :=
    (openOperatorEquiv C p (base C) U).bijective.comp
      ((operatorModuleSections (sheafFrobenius C p (base C)) U).bijective.comp hb)
  have he : (fun r : Γ(affine C, U) =>
      openOperatorEquiv C p (base C) U
        (operatorModuleSections (sheafFrobenius C p (base C)) U
          (((affineTraceFrame C p).val.app (op U)).hom r))) =
      (fun r => ((trace C p).restrict U).inputWeight (U.topIso.inv r)) := by
    funext r
    ext V m
    have ho := openOperatorEquiv_apply C p (base C) U
      (operatorModuleSections (sheafFrobenius C p (base C)) U
        (((affineTraceFrame C p).val.app (op U)).hom r)) V m
    have ha := affineTraceFrame_apply C p U r
      (Over.mk (homOfLE (U.ι_image_le V)))
      (show Γ(affine C, U.ι ''ᵁ V) from m)
    have hr : U.toScheme.presheaf.map V.leTop.op (U.topIso.inv r) =
        (affine C).presheaf.map (homOfLE (U.ι_image_le V)).op r := by
      rw [Scheme.Opens.topIso_inv]
      change (affine C).presheaf.map (U.ι.opensFunctor.map V.leTop).op
          ((affine C).presheaf.map (eqToHom U.ι_image_top).op r) = _
      rw [← CommRingCat.comp_apply, ← (affine C).presheaf.map_comp]
      rfl
    have hm : (trace C p).onOpen (U.ι ''ᵁ V)
        ((affine C).presheaf.map (homOfLE (U.ι_image_le V)).op r *
          (show Γ(affine C, U.ι ''ᵁ V) from m)) =
        (((trace C p).restrict U).inputWeight (U.topIso.inv r)).onOpen V m := by
      rw [SchemeFrobeniusMap.inputWeight_apply]
      change (trace C p).onOpen (U.ι ''ᵁ V)
          ((affine C).presheaf.map (homOfLE (U.ι_image_le V)).op r *
            (show Γ(affine C, U.ι ''ᵁ V) from m)) =
        (trace C p).onOpen (U.ι ''ᵁ V)
          (U.toScheme.presheaf.map V.leTop.op (U.topIso.inv r) * m)
      rw [hr]
      rfl
    exact ho.trans (ha.trans hm)
  exact he ▸ hf

end FrobeniusSplitting.OperatorSheaf
