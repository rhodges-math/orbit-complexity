import OrbitComplexity.FrobeniusSplitting.Normality.Models.PriorPatchModels
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorSectionNaturality

/-! # Retained principal patches on the proper prior scheme -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem principal_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) (hs : f.appTop.hom r = s) :
    ∃ d : (X.basicOpen s).toScheme ⟶ (Y.basicOpen r).toScheme,
      d ≫ (Y.basicOpen r).ι = (X.basicOpen s).ι ≫ f ∧
      IsPullback d (X.basicOpen s).ι (Y.basicOpen r).ι f := by
  have hp : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen s := by
    rw [Scheme.preimage_basicOpen_top, hs]
  let e := X.isoOfEq hp
  let d := e.inv ≫ f ∣_ Y.basicOpen r
  have hd : d ≫ (Y.basicOpen r).ι = (X.basicOpen s).ι ≫ f := by
    dsimp only [d]
    rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc]
  refine ⟨d, hd, IsOpenImmersion.isPullback d _ _ f hd.symm ?_⟩
  simpa only [Scheme.Opens.opensRange_ι] using hp

/-- The chosen principal refinement is realized on the coefficient
base change of the proper prior scheme, with cartesian patch maps. -/
theorem exists_prior_principal_realization {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {Y YK : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ i, IsAffine (U.X i))
    (V : YK.OpenCover.{u}) :
    let Q : YK.OpenCover.{u} := U.pullback₂ qY
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
      let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
      let YR := pullback base sr
      let qR := pullback.fst base sr
      let baseR := pullback.snd base sr
      let QR : YR.OpenCover.{u} := U.pullback₂ qR
      R.FG ∧ ∃ (m : YK ⟶ YR) (d : ∀ i, Q.X i ⟶ QR.X i),
        IsProper baseR ∧ IsPullback m baseK baseR kr ∧ m ≫ qR = qY ∧
        (∀ i, d i ≫ QR.f i = Q.f i ≫ m) ∧
      ∃ (L : Type u) (_ : Finite L) (prior : L → U.I₀) (endpoint : L → V.I₀)
        (s : ∀ l, Γ(Q.X (prior l), ⊤)) (r : ∀ l, Γ(QR.X (prior l), ⊤))
        (a : ∀ l, ((Q.X (prior l)).basicOpen (s l)).toScheme ⟶ V.X (endpoint l))
        (p : ∀ l, ((Q.X (prior l)).basicOpen (s l)).toScheme ⟶
          ((QR.X (prior l)).basicOpen (r l)).toScheme),
        (∀ l, (d (prior l)).appTop.hom (r l) = s l) ∧
        (∀ l, ((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l) = a l ≫ V.f (endpoint l)) ∧
        (∀ l, p l ≫ ((QR.X (prior l)).basicOpen (r l)).ι =
          ((Q.X (prior l)).basicOpen (s l)).ι ≫ d (prior l)) ∧
        (∀ l, IsPullback (p l) ((Q.X (prior l)).basicOpen (s l)).ι
          ((QR.X (prior l)).basicOpen (r l)).ι (d (prior l))) ∧
        (∀ l, p l ≫ (((QR.X (prior l)).basicOpen (r l)).ι ≫ QR.f (prior l)) =
          (((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l)) ≫ m) ∧
        ∀ y : YK, ∃ l, ∃ z : ((Q.X (prior l)).basicOpen (s l)).toScheme,
          (((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l)) z = y := by
  classical
  let Q : YK.OpenCover.{u} := U.pullback₂ qY
  let (i : U.I₀) : IsAffine (U.X i) := hU i
  let (i : U.I₀) : Algebra S Γ(U.X i, ⊤) :=
    ((U.f i ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let (i : U.I₀) : Algebra K Γ(Q.X i, ⊤) :=
    ((Q.f i ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let bK : ∀ i, Q.X i ⟶ U.X i := fun i ↦ pullback.fst (U.f i) qY
  obtain ⟨e, he, R, hSR, hR, L, hL, prior, endpoint, s, g, a, hg, ha, hcover⟩ :=
    exists_prior_patch_models S hS base baseK qY h U hU V
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let YR := pullback base sr
  let qR := pullback.fst base sr
  let baseR := pullback.snd base sr
  let QR : YR.OpenCover.{u} := U.pullback₂ qR
  let bR : ∀ i, QR.X i ⟶ U.X i := fun i ↦ pullback.fst (U.f i) qR
  let (i : U.I₀) : Algebra R Γ(QR.X i, ⊤) :=
    ((QR.f i ≫ baseR).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  obtain ⟨m, hmproper, hmcart, hm, hmbase, hcharts⟩ :=
    exists_prior_scalar_extension (R := R) base baseK qY h
  have charts (i : U.I₀) : ∃ d : Q.X i ⟶ QR.X i,
      d ≫ bR i = bK i ∧ d ≫ QR.f i = Q.f i ≫ m ∧
      IsPullback d (Q.f i ≫ baseK) (QR.f i ≫ baseR) kr := hcharts (U.X i) (U.f i)
  choose d hd hdleg hdcart using charts
  have coords (i : U.I₀) : ∃
      (eR : R ⊗[S] Γ(U.X i, ⊤) ≃ₐ[R] Γ(QR.X i, ⊤))
      (eK : K ⊗[S] Γ(U.X i, ⊤) ≃ₐ[K] Γ(Q.X i, ⊤)),
      (∀ r x, eR (r ⊗ₜ[S] x) =
        algebraMap R Γ(QR.X i, ⊤) r * (bR i).appTop.hom x) ∧
      (∀ k x, eK (k ⊗ₜ[S] x) =
        algebraMap K Γ(Q.X i, ⊤) k * (bK i).appTop.hom x) ∧
      ∀ z, (d i).appTop.hom (eR z) =
        eK (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S Γ(U.X i, ⊤)) z) := by
    have hpR : IsPullback (bR i) (QR.f i ≫ baseR) (U.f i ≫ base) sr :=
      (IsPullback.of_hasPullback (U.f i) qR).paste_vert
        (IsPullback.of_hasPullback base sr)
    have hpK : IsPullback (bK i) (Q.f i ≫ baseK) (U.f i ≫ base)
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) :=
      (IsPullback.of_hasPullback (U.f i) qY).paste_vert h
    have ht : d i ≫ (QR.f i ≫ baseR) = (Q.f i ≫ baseK) ≫ kr := by
      rw [← Category.assoc, hdleg, Category.assoc, hmbase, Category.assoc]
    exact exists_prior_section_comparison (U.f i ≫ base) (QR.f i ≫ baseR)
      (Q.f i ≫ baseK) (bR i) (bK i) (d i) hpR hpK (hd i) ht
  choose eR eK heR heK heval using coords
  have hsame (i : U.I₀) (z : K ⊗[S] Γ(U.X i, ⊤)) : eK i z = e i z := by
    induction z using TensorProduct.inductionOn with
    | tmul k x => exact (heK i k x).trans (he i k x).symm
    | add a b ha hb => simp only [map_add, ha, hb]
  let r (l : L) := eR (prior l) (g l)
  have hr (l : L) : (d (prior l)).appTop.hom (r l) = s l := by
    exact (heval (prior l) (g l)).trans ((hsame (prior l) _).trans (hg l))
  choose p hp hpcart using fun l ↦ principal_restriction (d (prior l)) (r l) (s l) (hr l)
  refine ⟨R, hSR, hR, m, d, hmproper, hmcart, hm, hdleg,
    L, hL, prior, endpoint, s, r, a, p, hr, ha, hp, hpcart, ?_, hcover⟩
  intro l
  rw [← Category.assoc, hp, Category.assoc, hdleg, ← Category.assoc]

end FrobeniusSplitting
