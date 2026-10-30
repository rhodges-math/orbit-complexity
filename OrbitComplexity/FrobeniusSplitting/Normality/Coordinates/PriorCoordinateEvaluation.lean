import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorSectionNaturality

/-! # evaluation through the same prior coordinate presentation -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- The chart map evaluates the enlarged coordinates through the original
comparison, with no independently chosen presentation identification. -/
theorem prior_coordinate_evaluation {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {W WR WK : Scheme.{u}} [IsAffine W]
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
      ∀ g : R ⊗[S] Γ(W, ⊤), m.appTop.hom (d g) =
        ((Algebra.TensorProduct.cancelBaseChange S R K K Γ(W, ⊤)).trans e)
          ((1 : K) ⊗ₜ[R] g) := by
  let : Algebra S Γ(W, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : Algebra R Γ(WR, ⊤) :=
    (tR.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(WK, ⊤) :=
    (tK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro d e hd he g
  obtain ⟨d0, e0, hd0, he0, H⟩ := exists_prior_section_comparison f tR tK qR qK m hR hK hm ht
  have hde : d = d0 := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x => rw [hd, hd0]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hee : e = e0 := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul k x => rw [he, he0]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hval (z : R ⊗[S] Γ(W, ⊤)) :
      ((Algebra.TensorProduct.cancelBaseChange S R K K Γ(W, ⊤)).trans e)
          ((1 : K) ⊗ₜ[R] z) =
        e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S Γ(W, ⊤)) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        change e (Algebra.TensorProduct.cancelBaseChange S R K K Γ(W, ⊤)
          ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] x))) = e (algebraMap R K r ⊗ₜ[S] x)
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        congr 1
        simp only [Algebra.smul_def, mul_one]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  rw [hval, hde, hee]
  exact H g

end FrobeniusSplitting
