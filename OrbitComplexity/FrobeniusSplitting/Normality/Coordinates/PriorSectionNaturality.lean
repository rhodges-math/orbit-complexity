import OrbitComplexity.FrobeniusSplitting.Normality.Models.PriorScalarExtension

/-! # coefficient-extension squares on the prior affine chart sections -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- The tensor coordinates of both scalar pullbacks commute with the
map of prior affine charts. This applies to every retained principal function. -/
theorem exists_prior_section_comparison {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {W WR WK : Scheme.{u}} [IsAffine W]
    (f : W ⟶ Spec (.of S)) (tR : WR ⟶ Spec (.of R)) (tK : WK ⟶ Spec (.of K))
    (qR : WR ⟶ W) (qK : WK ⟶ W) (d : WK ⟶ WR)
    (hR : IsPullback qR tR f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hK : IsPullback qK tK f (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hd : d ≫ qR = qK)
    (ht : d ≫ tR = tK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    letI : Algebra S Γ(W, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : Algebra R Γ(WR, ⊤) :=
      (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra K Γ(WK, ⊤) :=
      (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ (eR : R ⊗[S] Γ(W, ⊤) ≃ₐ[R] Γ(WR, ⊤))
      (eK : K ⊗[S] Γ(W, ⊤) ≃ₐ[K] Γ(WK, ⊤)),
      (∀ r x, eR (r ⊗ₜ[S] x) = algebraMap R Γ(WR, ⊤) r * qR.appTop.hom x) ∧
      (∀ k x, eK (k ⊗ₜ[S] x) = algebraMap K Γ(WK, ⊤) k * qK.appTop.hom x) ∧
      ∀ g : R ⊗[S] Γ(W, ⊤), d.appTop.hom (eR g) =
        eK (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S Γ(W, ⊤)) g) := by
  let : Algebra S Γ(W, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ(WR, ⊤) :=
    (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(WK, ⊤) :=
    (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  obtain ⟨eR, _, _, heR⟩ := exists_affine_scalar_coordinates f tR qR hR
  obtain ⟨eK, _, _, heK⟩ := exists_affine_scalar_coordinates f tK qK hK
  have hcoeff (r : R) : d.appTop.hom (algebraMap R Γ(WR, ⊤) r) =
      algebraMap K Γ(WK, ⊤) (algebraMap R K r) := by
    change (d ≫ tR).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) = _
    rw [ht]
    change tK.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop.hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r)) = _
    have H := congrArg (fun g : CommRingCat.of R ⟶ Γ(Spec (.of K), ⊤) ↦ g.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    exact congrArg tK.appTop.hom H.symm
  have hcoord (x : Γ(W, ⊤)) : d.appTop.hom (qR.appTop.hom x) = qK.appTop.hom x :=
    congrArg (fun g : WK ⟶ W ↦ g.appTop.hom x) hd
  refine ⟨eR, eK, heR, heK, fun g ↦ ?_⟩
  induction g using TensorProduct.inductionOn with
  | tmul r x =>
      rw [heR, map_mul, hcoeff, hcoord, Algebra.TensorProduct.map_tmul, heK]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end FrobeniusSplitting
