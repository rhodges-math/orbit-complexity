import Mathlib.AlgebraicGeometry.Restrict

/-! # Section transport through open-subscheme coordinates -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

/-- Restriction through open-subscheme global sections agrees with ambient restriction. -/
theorem homOfLE_topIso_inv {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) :
    (X.homOfLE h).appTop (U.topIso.inv r) =
      V.topIso.inv (X.presheaf.map (homOfLE h).op r) := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv]
  have hl := X.presheaf.map_comp (eqToHom U.ι_image_top).op
    (homOfLE (X.ι_image_homOfLE_le_ι_image h ⊤)).op
  have hr := X.presheaf.map_comp (homOfLE h).op (eqToHom V.ι_image_top).op
  exact congrArg (fun k : Γ(X, U) ⟶ Γ(X, V.ι ''ᵁ ⊤) => k r) (hl.symm.trans hr)

/-- Restricting a scheme morphism commutes with the global-section open identifications. -/
theorem morphismRestrict_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (r : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv r) = (f ⁻¹ᵁ U).topIso.inv (f.app U r) := by
  rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv]
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (f.app (U.ι ''ᵁ ⊤) (Y.presheaf.map (eqToHom U.ι_image_top).op r)) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Category.assoc, f.naturality, Category.assoc, ← X.presheaf.map_comp]
  rfl

/-- The open inclusion restricts ambient global sections through the section isomorphism. -/
theorem inclusion_topIso_inv {X : Scheme.{u}} (U : X.Opens) (t : Γ(X, ⊤)) :
    U.ι.appTop t = U.topIso.inv (X.presheaf.map U.leTop.op t) := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  have h := X.presheaf.map_comp U.leTop.op (eqToHom U.ι_image_top).op
  exact congrArg (fun k : Γ(X, ⊤) ⟶ Γ(X, U.ι ''ᵁ ⊤) => k t) h

/-- A weight transported by a range isomorphism pulls back to its original restrictions. -/
theorem openRangeWeight_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (e : X ≅ U.toScheme) (he : e.hom ≫ U.ι = f) (t : Γ(X, ⊤))
    (W : Y.Opens) (hW : W ≤ U) :
    f.app W (Y.presheaf.map (homOfLE hW).op (U.topIso.hom (e.inv.appTop t))) =
      X.presheaf.map (f ⁻¹ᵁ W).leTop.op t := by
  let r : Γ(Y, U) := U.topIso.hom (e.inv.appTop t)
  have hfac : (f ∣_ W) ≫ Y.homOfLE hW = (f ⁻¹ᵁ W).ι ≫ e.hom := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc, he]
  have hcat : ((f ∣_ W) ≫ Y.homOfLE hW) ≫ e.inv = (f ⁻¹ᵁ W).ι := by
    rw [hfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ha := congrArg
    (fun k : (f ⁻¹ᵁ W).toScheme ⟶ X => k.appTop t) hcat
  change (f ∣_ W).appTop ((Y.homOfLE hW).appTop (e.inv.appTop t)) =
    (f ⁻¹ᵁ W).ι.appTop t at ha
  have hu : U.topIso.inv r = e.inv.appTop t :=
    U.topIso.commRingCatIsoToRingEquiv.symm_apply_apply _
  have hr := ((congrArg (Y.homOfLE hW).appTop hu).symm).trans
    (homOfLE_topIso_inv hW r)
  have hc := (morphismRestrict_topIso_inv f W
    (Y.presheaf.map (homOfLE hW).op r)).symm.trans
      ((congrArg (f ∣_ W).appTop hr).symm.trans ha)
  have ht := hc.trans (inclusion_topIso_inv (f ⁻¹ᵁ W) t)
  exact (f ⁻¹ᵁ W).topIso.commRingCatIsoToRingEquiv.symm.injective ht

end FrobeniusSplitting.OperatorSheaf
