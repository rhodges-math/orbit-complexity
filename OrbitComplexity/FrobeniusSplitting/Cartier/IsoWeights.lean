import OrbitComplexity.FrobeniusSplitting.Cartier.AffineWeights
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionTransport

/-! # Input trace weights in isomorphic open coordinates -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.SchemeFrobeniusMap

private theorem transported_restrict {X Y : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (e : X ≅ Y) (U : Y.Opens) :
    ((φ.pushforward e.hom).restrict U).openPullback (e.hom ∣_ U) =
      φ.restrict (e.hom ⁻¹ᵁ U) := by
  have ht : (φ.pushforward e.hom).openPullback e.hom = φ :=
    (operatorIsoEquiv (p := p) e).left_inv φ
  calc
    ((φ.pushforward e.hom).restrict U).openPullback (e.hom ∣_ U) =
        (φ.pushforward e.hom).openPullback ((e.hom ∣_ U) ≫ U.ι) := by
      rw [openPullback_comp, openPullback_restrict]
    _ = (φ.pushforward e.hom).openPullback ((e.hom ⁻¹ᵁ U).ι ≫ e.hom) := by
      congr 1
      exact morphismRestrict_ι e.hom U
    _ = φ.restrict (e.hom ⁻¹ᵁ U) := by
      rw [openPullback_comp, ht, openPullback_restrict]

/-- Bijection of input weights passes through isomorphic scheme coordinates. -/
theorem inputWeight_open_bijective_iso {X Y : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (e : X ≅ Y) (U : Y.Opens)
    (h : Function.Bijective (fun r : Γ(X, e.hom ⁻¹ᵁ U) =>
      (φ.restrict (e.hom ⁻¹ᵁ U)).inputWeight ((e.hom ⁻¹ᵁ U).topIso.inv r))) :
    Function.Bijective (fun r : Γ(Y, U) =>
      ((φ.pushforward e.hom).restrict U).inputWeight (U.topIso.inv r)) := by
  let er := (asIso (e.hom.app U)).commRingCatIsoToRingEquiv
  let eo := (operatorIsoEquiv (p := p) (asIso (e.hom ∣_ U))).symm
  have hw (r : Γ(Y, U)) :
      eo (((φ.pushforward e.hom).restrict U).inputWeight (U.topIso.inv r)) =
        (φ.restrict (e.hom ⁻¹ᵁ U)).inputWeight
          ((e.hom ⁻¹ᵁ U).topIso.inv (er r)) := by
    change (((φ.pushforward e.hom).restrict U).inputWeight
      (U.topIso.inv r)).openPullback (e.hom ∣_ U) = _
    rw [openPullback_inputWeight, transported_restrict]
    exact congrArg (φ.restrict (e.hom ⁻¹ᵁ U)).inputWeight
      (OperatorSheaf.morphismRestrict_topIso_inv e.hom U r)
  have he : (fun r : Γ(Y, U) =>
      ((φ.pushforward e.hom).restrict U).inputWeight (U.topIso.inv r)) =
      (fun r => eo.symm ((φ.restrict (e.hom ⁻¹ᵁ U)).inputWeight
        ((e.hom ⁻¹ᵁ U).topIso.inv (er r)))) := by
    funext r
    exact eo.injective ((hw r).trans (eo.apply_symm_apply _).symm)
  rw [he]
  exact eo.symm.bijective.comp (h.comp er.bijective)

/-- Input-weight coordinates on an open range pull back to the source scheme. -/
theorem inputWeight_bijective_openPullback {X Y : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap Y p) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : Function.Bijective (fun r : Γ(Y, f.opensRange) =>
      (φ.restrict f.opensRange).inputWeight (f.opensRange.topIso.inv r))) :
    Function.Bijective (fun r : Γ(X, ⊤) => (φ.openPullback f).inputWeight r) := by
  let e := f.isoOpensRange
  let er := f.opensRange.topIso.commRingCatIsoToRingEquiv.symm.trans
    (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  let eo := (operatorIsoEquiv (p := p) e).symm
  have hf : (φ.restrict f.opensRange).openPullback e.hom = φ.openPullback f := by
    rw [← openPullback_restrict, ← openPullback_comp]
    congr 1
    exact f.isoOpensRange_hom_ι
  have hw (r : Γ(Y, f.opensRange)) :
      eo ((φ.restrict f.opensRange).inputWeight (f.opensRange.topIso.inv r)) =
        (φ.openPullback f).inputWeight (er r) := by
    change ((φ.restrict f.opensRange).inputWeight
      (f.opensRange.topIso.inv r)).openPullback e.hom = _
    rw [openPullback_inputWeight, hf]
    rfl
  have he : (fun r : Γ(X, ⊤) => (φ.openPullback f).inputWeight r) =
      (fun r => eo ((φ.restrict f.opensRange).inputWeight
        (f.opensRange.topIso.inv (er.symm r)))) := by
    funext r
    have ht := (hw (er.symm r)).symm
    exact (congrArg (φ.openPullback f).inputWeight (er.apply_symm_apply r)).symm.trans ht
  rw [he]
  exact eo.bijective.comp (h.comp er.symm.bijective)

end FrobeniusSplitting.SchemeFrobeniusMap

namespace FrobeniusSplitting.OperatorSheaf

/-- Transported polynomial trace weights parametrize all operators on each open. -/
theorem affineTrace_iso_weight_open_bijective (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] [PerfectRing C p] {Y : Scheme.{u}}
    (e : Spec (.of (Polynomial C)) ≅ Y) (U : Y.Opens) :
    Function.Bijective (fun r : Γ(Y, U) =>
      ((((univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec
        (expChar_pos C p)).pushforward e.hom).restrict U).inputWeight (U.topIso.inv r)) :=
  SchemeFrobeniusMap.inputWeight_open_bijective_iso _ e U
    (affineTrace_weight_open_bijective C p (e.hom ⁻¹ᵁ U))

end FrobeniusSplitting.OperatorSheaf
