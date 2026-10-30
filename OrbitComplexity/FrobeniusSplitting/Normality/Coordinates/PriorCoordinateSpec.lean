import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorCoordinateEvaluation

/-! # The spectrum square for the original prior coordinates -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- The original tensor coordinate comparison gives the affine spectrum square,
including the chosen enlarged coordinates, before postcomposing with a global chart. -/
theorem prior_coordinate_spec {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {W WR WK : Scheme.{u}} [IsAffine W] [IsAffine WR] [IsAffine WK]
    (f : W ⟶ Spec (.of S)) (tR : WR ⟶ Spec (.of R)) (tK : WK ⟶ Spec (.of K))
    (qR : WR ⟶ W) (qK : WK ⟶ W) (m : WK ⟶ WR)
    (hR : IsPullback qR tR f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hK : IsPullback qK tK f (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hm : m ≫ qR = qK)
    (ht : m ≫ tR = tK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    letI : Algebra S Γ(W, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra R Γ(WR, ⊤) :=
      (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra K Γ(WK, ⊤) :=
      (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (d : R ⊗[S] Γ(W, ⊤) ≃ₐ[R] Γ(WR, ⊤))
      (e : K ⊗[S] Γ(W, ⊤) ≃ₐ[K] Γ(WK, ⊤)),
      (∀ r x, d (r ⊗ₜ[S] x) = algebraMap R Γ(WR, ⊤) r * qR.appTop.hom x) →
      (∀ k x, e (k ⊗ₜ[S] x) = algebraMap K Γ(WK, ⊤) k * qK.appTop.hom x) →
      let eval := ((Algebra.TensorProduct.cancelBaseChange S R K K Γ(W, ⊤)).trans e).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom
      Spec.map (CommRingCat.ofHom eval) ≫
          Spec.map (CommRingCat.ofHom d.symm.toRingHom) ≫ WR.isoSpec.inv =
        WK.isoSpec.inv ≫ m := by
  let : Algebra S Γ(W, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ(WR, ⊤) :=
    (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(WK, ⊤) :=
    (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro d e hd he
  let eval := ((Algebra.TensorProduct.cancelBaseChange S R K K Γ(W, ⊤)).trans e).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom
  have H : CommRingCat.ofHom eval = CommRingCat.ofHom d.toRingHom ≫ m.appTop := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (prior_coordinate_evaluation f tR tK qR qK m hR hK hm ht d e hd he x).symm
  let D : Spec Γ(WR, ⊤) ≅ Spec (.of (R ⊗[S] Γ(W, ⊤))) :=
    Scheme.Spec.mapIso d.toRingEquiv.toCommRingCatIso.op
  have hSpec : Spec.map (CommRingCat.ofHom eval) = Spec.map m.appTop ≫ D.hom := by
    rw [H, Spec.map_comp]
    rfl
  change Spec.map (CommRingCat.ofHom eval) ≫ D.inv ≫ WR.isoSpec.inv = _
  rw [hSpec]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using Scheme.isoSpec_inv_naturality m

end FrobeniusSplitting
