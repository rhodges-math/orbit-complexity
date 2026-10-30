import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorPrincipalRealization
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorCoefficientCover

/-! # A compatible affine cover on a base change of the proper prior scheme -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem chart_pullback {W Y YK YR : Scheme.{u}}
    (a : W ⟶ Y) [Mono a] (qK : YK ⟶ Y) (qR : YR ⟶ Y) (m : YK ⟶ YR)
    (hm : m ≫ qR = qK) (d : pullback a qK ⟶ pullback a qR)
    (hd : d ≫ pullback.snd a qR = pullback.snd a qK ≫ m) :
    IsPullback d (pullback.snd a qK) (pullback.snd a qR) m := by
  have hf : d ≫ pullback.fst a qR = pullback.fst a qK := by
    apply (cancel_mono a).mp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hd,
      Category.assoc, hm, ← pullback.condition]
  have H : IsPullback (d ≫ pullback.fst a qR) (pullback.snd a qK) a (m ≫ qR) := by
    rw [hf, hm]
    exact IsPullback.of_hasPullback a qK
  exact H.of_right hd (IsPullback.of_hasPullback a qR)

/-- A finite affine cover refining the same endpoint charts exists on an
base change of the prior proper model. It covers after every subsequent scheme base change. -/
theorem exists_prior_refined_cover {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {Y YK : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [LocallyOfFinitePresentation base]
    (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ i, IsAffine (U.X i))
    (V : YK.OpenCover.{u}) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
        (qT : YT ⟶ Y) (mT : YK ⟶ YT),
        IsProper baseT ∧ LocallyOfFinitePresentation baseT ∧
        IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
        IsPullback mT baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
        mT ≫ qT = qY ∧
      ∃ (W : YT.OpenCover.{u}) (_ : Finite W.I₀) (_ : ∀ l, IsAffine (W.X l))
        (prior : W.I₀ → U.I₀) (endpoint : W.I₀ → V.I₀)
        (XK : W.I₀ → Scheme.{u}) (fK : ∀ l, XK l ⟶ YK)
        (qX : ∀ l, XK l ⟶ W.X l) (a : ∀ l, XK l ⟶ V.X (endpoint l))
        (b : ∀ l, XK l ⟶ U.X (prior l)),
        (∀ l, IsPullback (qX l) (fK l) (W.f l) mT) ∧
        (∀ l, fK l = a l ≫ V.f (endpoint l)) ∧
        (∀ l, fK l ≫ qY = b l ≫ U.f (prior l)) ∧
        (∀ y : YK, ∃ l x, fK l x = y) ∧
        ∀ (Z : Scheme.{u}) (g : Z ⟶ YT) (z : Z),
          ∃ l, ∃ x : (pullback (W.f l) g : Scheme.{u}), (pullback.snd (W.f l) g) x = z := by
  classical
  let Q : YK.OpenCover.{u} := U.pullback₂ qY
  obtain ⟨R, hSR, hR, m, d, hproper, hcart, hm, hd,
    L, hL, prior, endpoint, s, r, a, p, _, ha, _, hp, hcomm, hcover⟩ :=
    exists_prior_principal_realization S hS base baseK qY h U hU V
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let qR := pullback.fst base sr
  let baseR := pullback.snd base sr
  let QR : YR.OpenCover.{u} := U.pullback₂ qR
  let : Finite L := hL
  let X (l : L) := ((QR.X (prior l)).basicOpen (r l)).toScheme
  let XK (l : L) := ((Q.X (prior l)).basicOpen (s l)).toScheme
  let f (l : L) : X l ⟶ YR := ((QR.X (prior l)).basicOpen (r l)).ι ≫ QR.f (prior l)
  let fK (l : L) : XK l ⟶ YK := ((Q.X (prior l)).basicOpen (s l)).ι ≫ Q.f (prior l)
  have hchart (i : U.I₀) : IsPullback (d i) (Q.f i) (QR.f i) m := by
    have : IsOpenImmersion (U.f i) := U.map_prop i
    exact chart_pullback (U.f i) qY qR m hm (d i) (hd i)
  have hpatch (l : L) : IsPullback (p l) (fK l) (f l) m :=
    (hp l).paste_vert (hchart (prior l))
  have affineR (i : U.I₀) : IsAffine (QR.X i) := by
    have : IsAffine (U.X i) := hU i
    exact IsAffine.of_isPullback
      ((IsPullback.of_hasPullback (U.f i) qR).paste_vert (IsPullback.of_hasPullback base sr))
  let (l : L) : IsAffine (X l) := by have := affineR (prior l); infer_instance
  let (l : L) : IsOpenImmersion (f l) := by
    have : IsOpenImmersion (QR.f (prior l)) := QR.map_prop _
    dsimp only [f]
    infer_instance
  have : IsProper baseR := hproper
  have : LocallyOfFinitePresentation baseR := inferInstance
  have : YR.IsSeparated := ⟨by
    rw [← terminal.comp_from baseR]
    infer_instance⟩
  have : CompactSpace YR := QuasiCompact.compactSpace_of_compactSpace baseR
  obtain ⟨T, hRT, hT, hcoverT⟩ := exists_prior_coefficient_cover R hR
    X XK f fK baseR p m baseK hcart hcomm hcover
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  let hST : S ≤ T := hSR.trans hRT
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let rt := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let YT := pullback baseR rt
  let qt := pullback.fst baseR rt
  let baseT := pullback.snd baseR rt
  obtain ⟨mT, hmproper, hmcart, hmt, _, _⟩ :=
    exists_prior_scalar_extension (R := T) baseR baseK m hcart
  have hc : ∀ y : YT, ∃ l, ∃ x : (pullback (f l) qt : Scheme.{u}), (pullback.snd (f l) qt) x = y :=
    hcoverT T
  let W : YT.OpenCover.{u} := Scheme.Cover.mkOfCovers L
    (fun l ↦ pullback (f l) qt) (fun l ↦ pullback.snd (f l) qt) hc
  have haff (l : W.I₀) : IsAffine (W.X l) :=
    IsAffine.of_isPullback
      ((IsPullback.of_hasPullback (f l) qt).paste_vert (IsPullback.of_hasPullback baseR rt))
  have maps (l : L) : ∃ q : XK l ⟶ W.X l,
      IsPullback q (fK l) (W.f l) mT := by
    have H : IsPullback (p l) (fK l) (f l) (mT ≫ qt) := by rw [hmt]; exact hpatch l
    let HP := IsPullback.of_hasPullback (f l) qt
    exact ⟨HP.lift (p l) (fK l ≫ mT) (by simpa only [Category.assoc] using H.w),
      IsPullback.of_right' H HP⟩
  choose qX hqX using maps
  have hcoeff : rt ≫ sr = Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hprior : IsPullback (qt ≫ qR) baseT base
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [← hcoeff]
    exact (IsPullback.of_hasPullback baseR rt).paste_horiz (IsPullback.of_hasPullback base sr)
  let bK : ∀ i, Q.X i ⟶ U.X i := fun i ↦ pullback.fst (U.f i) qY
  let b (l : L) : XK l ⟶ U.X (prior l) :=
    ((Q.X (prior l)).basicOpen (s l)).ι ≫ bK (prior l)
  have hQ (i : U.I₀) : Q.f i ≫ qY = bK i ≫ U.f i :=
    (pullback.condition (f := U.f i) (g := qY)).symm
  have hB (l : L) : fK l ≫ qY = b l ≫ U.f (prior l) := by
    calc
      fK l ≫ qY = ((Q.X (prior l)).basicOpen (s l)).ι ≫ (Q.f (prior l) ≫ qY) :=
        Category.assoc _ _ _
      _ = ((Q.X (prior l)).basicOpen (s l)).ι ≫ (bK (prior l) ≫ U.f (prior l)) :=
        congrArg (fun z : Q.X (prior l) ⟶ Y ↦ ((Q.X (prior l)).basicOpen (s l)).ι ≫ z)
          (hQ (prior l))
      _ = b l ≫ U.f (prior l) := (Category.assoc _ _ _).symm
  refine ⟨T, hST, hT, YT, baseT, qt ≫ qR, mT, hmproper, inferInstance,
    hprior, hmcart, ?_, W, hL, haff, prior, endpoint, XK, fK, qX, a,
    b, hqX, ha, hB, hcover, ?_⟩
  · rw [← Category.assoc, hmt, hm]
  · intro Z g z
    exact Scheme.Cover.exists_eq (W.pullback₂ g : Z.OpenCover.{u}) z

end FrobeniusSplitting
