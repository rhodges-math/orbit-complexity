import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorCoordinateSpec

/-! # open-coordinate legs under the retained prior scalar comparison -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- On an original affine open, both scalar inverse images give the same
/model coordinate leg, with the original generic tensor presentation. -/
theorem prior_open_coordinate_leg {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {Y YK : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (baseK : YK ⟶ Spec (.of K)) (qK : YK ⟶ Y)
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    ∀ (m : YK ⟶ YR), m ≫ qR = qK →
      m ≫ baseR = baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) →
    let UR := qR ⁻¹ᵁ U
    let UK := qK ⁻¹ᵁ U
    let tR := UR.ι ≫ baseR
    let tK := UK.ι ≫ baseK
    letI : IsAffine U.toScheme := hU
    letI : Algebra S Γ(U.toScheme, ⊤) :=
      ((U.ι ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra R Γ(UR.toScheme, ⊤) :=
      (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra K Γ(UK.toScheme, ⊤) :=
      (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (d : R ⊗[S] Γ(U.toScheme, ⊤) ≃ₐ[R] Γ(UR.toScheme, ⊤))
      (e : K ⊗[S] Γ(U.toScheme, ⊤) ≃ₐ[K] Γ(UK.toScheme, ⊤)),
      (∀ r x, d (r ⊗ₜ[S] x) = algebraMap R Γ(UR.toScheme, ⊤) r *
        (qR ∣_ U).appTop.hom x) →
      (∀ k x, e (k ⊗ₜ[S] x) = algebraMap K Γ(UK.toScheme, ⊤) k *
        (qK ∣_ U).appTop.hom x) →
      letI : IsAffine UR.toScheme := IsAffine.of_isPullback
        ((isPullback_morphismRestrict qR U).paste_vert (IsPullback.of_hasPullback base sr))
      letI : IsAffine UK.toScheme := IsAffine.of_isPullback
        ((isPullback_morphismRestrict qK U).paste_vert hK)
      let e0 := (Algebra.TensorProduct.cancelBaseChange S R K K Γ(U.toScheme, ⊤)).trans e
      let eval := e0.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
      UK.toScheme.isoSpec.inv ≫ UK.ι ≫ m =
        Spec.map (CommRingCat.ofHom eval) ≫
          Spec.map (CommRingCat.ofHom d.symm.toRingHom) ≫ UR.toScheme.isoSpec.inv ≫ UR.ι := by
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let qR := pullback.fst base sr
  let baseR := pullback.snd base sr
  dsimp only
  intro m hm ht
  let UR := qR ⁻¹ᵁ U
  let UK := qK ⁻¹ᵁ U
  let tR := UR.ι ≫ baseR
  let tK := UK.ι ≫ baseK
  let : IsAffine U.toScheme := hU
  have hR : IsPullback (qR ∣_ U) tR (U.ι ≫ base) sr :=
    (isPullback_morphismRestrict qR U).paste_vert (IsPullback.of_hasPullback base sr)
  have hK' : IsPullback (qK ∣_ U) tK (U.ι ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) :=
    (isPullback_morphismRestrict qK U).paste_vert hK
  let : IsAffine UR.toScheme := IsAffine.of_isPullback hR
  let : IsAffine UK.toScheme := IsAffine.of_isPullback hK'
  let : Algebra S Γ(U.toScheme, ⊤) :=
    ((U.ι ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ(UR.toScheme, ⊤) :=
    (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(UK.toScheme, ⊤) :=
    (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro d e hd he
  let H := isPullback_morphismRestrict qR U
  have hcond : (qK ∣_ U) ≫ U.ι = (UK.ι ≫ m) ≫ qR := by
    rw [Category.assoc, hm, morphismRestrict_ι]
  let v : UK.toScheme ⟶ UR.toScheme := H.lift (qK ∣_ U) (UK.ι ≫ m) hcond
  have hv : v ≫ (qR ∣_ U) = qK ∣_ U := H.lift_fst _ _ _
  have hvι : v ≫ UR.ι = UK.ι ≫ m := H.lift_snd _ _ _
  have hvt : v ≫ tR = tK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    change v ≫ (UR.ι ≫ baseR) = (UK.ι ≫ baseK) ≫ _
    rw [← Category.assoc, hvι, Category.assoc, ht, Category.assoc]
  have hspec := prior_coordinate_spec (U.ι ≫ base) tR tK (qR ∣_ U) (qK ∣_ U) v
    hR hK' hv hvt d e hd he
  have Hleg := congrArg (fun f : Spec Γ(UK.toScheme, ⊤) ⟶ UR.toScheme ↦ f ≫ UR.ι) hspec
  simpa only [Category.assoc, hvι] using Hleg.symm

end FrobeniusSplitting
