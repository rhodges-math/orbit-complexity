import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Isomorphisms over dense open subsets

Isomorphisms over dense target opens persist on open subschemes. Restriction to
such an open subset is injective on sections of a reduced noetherian scheme.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-- An isomorphism over an open subset induces an isomorphism on its sections. -/
theorem app_isIso_of_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] : IsIso (f.app U) := by
  have h : IsIso ((f ∣_ U).app ⊤) := inferInstance
  rw [morphismRestrict_app] at h
  let e := X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U ⊤)).op
  have h' : IsIso (f.app (U.ι ''ᵁ ⊤)) :=
    (isIso_comp_right_iff (f.app (U.ι ''ᵁ ⊤)) e.hom).1 h
  rw [Scheme.Opens.ι_image_top] at h'
  exact h'

/-- Restriction to a dense open is injective on sections of a reduced noetherian scheme. -/
theorem restrict_injective {X : Scheme.{u}} [IsReduced X] [NoetherianSpace X]
    (U : X.Opens) (hdense : Dense (U : Set X)) :
    Function.Injective (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  have : IsDominant U.ι := Opens.isDominant_ι hdense
  have : IsSchemeTheoreticallyDominant U.ι := .of_isDominant _
  have : NoetherianSpace U.toScheme := by
    exact (Opens.isOpenEmbedding U).isInducing.noetherianSpace
  have : QuasiCompact U.ι := quasiCompact_of_noetherianSpace_source _
  have h := U.ι.app_injective ⊤
  have heq : U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    exact (X.presheaf.map_comp
      (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op
      (eqToHom U.ι_image_top.symm).op).symm
  rw [← heq]
  exact ((ConcreteCategory.isIso_iff_bijective U.topIso.hom).1 inferInstance).injective.comp h

/-- A morphism is an isomorphism over a dense open subset of its target. -/
def IsIsoOverDense {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsIso (f ∣_ U)

/-- An isomorphism over an open set remains so after restricting its target. -/
theorem isIso_restrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V ∣_ (V.ι ⁻¹ᵁ U)) := by
  have hfirst : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  have hsecond : IsIso (f ∣_ U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).1 hfirst
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V.ι ''ᵁ (V.ι ⁻¹ᵁ U) := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_comm]
  rw [heq] at hsecond
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).2 hsecond

/-- Being an isomorphism over a dense open set is preserved on open subschemes. -/
theorem IsIsoOverDense.restrict {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : IsIsoOverDense f) (V : Y.Opens) : IsIsoOverDense (f ∣_ V) := by
  obtain ⟨U, hdense, hiso⟩ := h
  exact ⟨V.ι ⁻¹ᵁ U, hdense.preimage (Opens.isOpenEmbedding V).isOpenMap,
    isIso_restrict_preimage f U V⟩

/-- An open isomorphism inside an injective morphism determines its restriction
to the target open. -/
theorem isIsoOverDense_of_openIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinjective : Function.Injective f) (U : X.Opens) (V : Y.Opens)
    (hdense : Dense (V : Set Y)) (e : U.toScheme ≅ V.toScheme)
    (hcommute : U.ι ≫ f = e.hom ≫ V.ι) : IsIsoOverDense f := by
  have hU : U ≤ f ⁻¹ᵁ V := by
    intro x hx
    have heq := congrArg (fun g : U.toScheme ⟶ Y ↦ g ⟨x, hx⟩) hcommute
    change f x = (e.hom ⟨x, hx⟩).1 at heq
    change f x ∈ V
    rw [heq]
    exact (e.hom ⟨x, hx⟩).2
  have heq : U = f ⁻¹ᵁ V := by
    apply le_antisymm hU
    intro x hx
    obtain ⟨u, hu⟩ := e.hom.surjective ⟨f x, hx⟩
    have hfx : f u.1 = f x := by
      calc
        f u.1 = V.ι (e.hom u) := congrArg (fun g : U.toScheme ⟶ Y ↦ g u) hcommute
        _ = f x := congrArg (fun y : V.toScheme ↦ y.1) hu
    rw [← hinjective hfx]
    exact u.2
  have hiso : IsIso (X.homOfLE hU) := by
    have hmap : X.homOfLE hU = (X.isoOfEq heq).hom := by
      apply (cancel_mono (f ⁻¹ᵁ V).ι).1
      simp
    rw [hmap]
    infer_instance
  have hres : f.resLE V U hU = e.hom := by
    apply (cancel_mono V.ι).1
    rw [Scheme.Hom.resLE_comp_ι, hcommute]
  have hrestricted : IsIso (f.resLE V U hU) := by rw [hres]; infer_instance
  change IsIso (X.homOfLE hU ≫ f ∣_ V) at hrestricted
  exact ⟨V, hdense, (isIso_comp_left_iff (X.homOfLE hU) (f ∣_ V)).1 hrestricted⟩

end FrobeniusSplitting
