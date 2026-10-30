import OrbitComplexity.FrobeniusSplitting.Normality.Models.EndpointPullbackRefinement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Endpoint refinements on the same proper prior model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting

/-- The same proper prior model has a finite affine cover whose
inverse images refine the specified endpoint charts. -/
theorem exists_prior_endpoint_opens {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {Y YK : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ j, IsAffine (U.X j))
    (V : YK.OpenCover.{u}) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
        (qT : YT ⟶ Y) (mT : YK ⟶ YT),
        IsProper baseT ∧ Smooth baseT ∧
        IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
        IsPullback mT baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
        mT ≫ qT = qY ∧
      ∃ (W : YT.OpenCover.{u}) (_ : Finite W.I₀) (_ : ∀ l, IsAffine (W.X l))
        (prior : W.I₀ → U.I₀) (endpoint : W.I₀ → V.I₀),
        let O : W.I₀ → YK.Opens := fun l ↦ mT ⁻¹ᵁ (W.f l).opensRange
        (⨆ l, O l) = ⊤ ∧ (∀ l, IsAffineOpen (O l)) ∧
        ∃ (a : ∀ l, (O l).toScheme ⟶ V.X (endpoint l))
          (b : ∀ l, (O l).toScheme ⟶ U.X (prior l))
          (q : ∀ l, (O l).toScheme ⟶ W.X l),
          (∀ l, a l ≫ V.f (endpoint l) = (O l).ι) ∧
          (∀ l, b l ≫ U.f (prior l) = (O l).ι ≫ qY) ∧
          (∀ l, IsPullback (q l) (O l).ι (W.f l) mT) ∧
          (∀ l, q l ≫ W.f l = (O l).ι ≫ mT) ∧
          ∀ (Z : Scheme.{u}) (g : Z ⟶ YT) (z : Z),
            ∃ l, ∃ x : (pullback (W.f l) g : Scheme.{u}),
              (pullback.snd (W.f l) g) x = z := by
  classical
  obtain ⟨T, hST, hT, YT, baseT, qT, mT, hproper, _, hTcart, hKcart, hmq,
    W, hfinite, haff, prior, endpoint, XK, fK, qX, a, b, hcart, ha, hb,
    hcover, hcoverAll⟩ := exists_prior_refined_cover S hS base baseK qY h U hU V
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : Finite W.I₀ := hfinite
  have hsmooth : Smooth baseT := MorphismProperty.of_isPullback hTcart inferInstance
  let O : W.I₀ → YK.Opens := fun l ↦ mT ⁻¹ᵁ (W.f l).opensRange
  have H (l : W.I₀) : ∃ e : XK l ≅ (O l).toScheme,
      e.hom ≫ (O l).ι = fK l ∧
      IsPullback (e.inv ≫ qX l) (O l).ι (W.f l) mT ∧
      (e.inv ≫ qX l) ≫ W.f l = (O l).ι ≫ mT ∧
      (e.inv ≫ a l) ≫ V.f (endpoint l) = (O l).ι := by
    let : IsOpenImmersion (W.f l) := W.map_prop l
    exact pullback_endpoint_refinement (W.f l) mT (qX l) (fK l) (hcart l)
      (a l) (V.f (endpoint l)) (ha l).symm
  choose e he hcartO hqO haO using H
  have hOcover : (⨆ l, O l) = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨l, x, hx⟩ := hcover y
    refine le_iSup O l ?_
    have hp : (O l).ι ((e l).hom x) = y := by
      rw [← Scheme.Hom.comp_apply, he l, hx]
    exact hp ▸ ((e l).hom x).property
  have hOaff (l : W.I₀) : IsAffineOpen (O l) := by
    have : IsAffine (W.X l) := haff l
    exact IsAffine.of_isPullback ((hcartO l).paste_vert hKcart)
  have hbO (l : W.I₀) : (e l).inv ≫ b l ≫ U.f (prior l) = (O l).ι ≫ qY := by
    rw [← hb l, ← Category.assoc]
    have hleg : (e l).inv ≫ fK l = (O l).ι := by
      rw [← he l]
      simp
    rw [hleg]
  refine ⟨T, hST, hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart,
    hmq, W, hfinite, haff, prior, endpoint, hOcover, hOaff,
    (fun l ↦ (e l).inv ≫ a l), (fun l ↦ (e l).inv ≫ b l),
    (fun l ↦ (e l).inv ≫ qX l), haO, hbO, hcartO, hqO, hcoverAll⟩

end FrobeniusSplitting
