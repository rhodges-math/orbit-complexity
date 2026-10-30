import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ScalarOpenIso
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedBirational
import Batteries.Tactic.OpenPrivate

/-! # Pointed open cells in scalar comparisons

Open isomorphisms and their sections are transported through Cartesian
comparisons. Endpoint squares factor through intermediate scalar models,
and a pointed isomorphism of model opens gives a common open cell.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u

open private lifted_cell_open from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.PointedBirational

private theorem inverse_projection {A B Z : Scheme.{u}} (E : A ≅ B)
    (p : B ⟶ Z) (q : A ⟶ Z) (h : E.hom ≫ p = q) : E.inv ≫ q = p := by
  rw [← h, Iso.inv_hom_id_assoc]

/-- A pointed open isomorphism is carried through two Cartesian scalar
comparisons, retaining its endpoint equation and its section. -/
theorem transport_pointed_open {B T : Scheme.{u}} (κ : T ⟶ B)
    (X Y : Over T) (C F : Over B)
    (qX : X.left ⟶ C.left) (qY : Y.left ⟶ F.left)
    (hX : IsPullback qX X.hom C.hom κ)
    (hY : IsPullback qY Y.hom F.hom κ)
    (e : C ⟶ F) (eT : X ⟶ Y) (he : eT.left ≫ qY = qX ≫ e.left)
    (U : C.left.Opens) (V : F.left.Opens)
    (A : X.left.Opens) (D : Y.left.Opens)
    (hA : qX ⁻¹ᵁ U = A) (hD : qY ⁻¹ᵁ V = D)
    (E : Over.mk (A.ι ≫ X.hom) ≅ Over.mk (D.ι ≫ Y.hom))
    (hE : E.hom.left ≫ D.ι = A.ι ≫ eT.left)
    (s : T ⟶ D.toScheme) (hs : s ≫ (D.ι ≫ Y.hom) = 𝟙 T) :
    ∃ (E0 : Over.mk (pullback.fst κ (U.ι ≫ C.hom)) ≅
        Over.mk (pullback.fst κ (V.ι ≫ F.hom)))
      (s0 : T ⟶ pullback κ (V.ι ≫ F.hom)),
      s0 ≫ pullback.fst κ (V.ι ≫ F.hom) = 𝟙 T ∧
      E0.hom.left ≫ pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι =
        pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι ≫ e.left := by
  obtain ⟨EU, hEU⟩ := exists_scalar_open_iso κ X C qX hX U A hA
  obtain ⟨EV, hEV⟩ := exists_scalar_open_iso κ Y F qY hY V D hD
  let E0 := EU.symm ≪≫ E ≪≫ EV
  let s0 := s ≫ EV.hom.left
  have hi : EU.inv.left ≫ (A.ι ≫ qX) =
      pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι :=
    inverse_projection ((Over.forget T).mapIso EU) _ _ hEU
  refine ⟨E0, s0, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => s ≫ a) EV.hom.w).trans hs)
  · change (EU.inv.left ≫ E.hom.left ≫ EV.hom.left) ≫
        pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι = _
    calc
      (EU.inv.left ≫ E.hom.left ≫ EV.hom.left) ≫
          pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι =
          EU.inv.left ≫ E.hom.left ≫ (D.ι ≫ qY) := by
        simpa only [Category.assoc] using
          congrArg (fun a => EU.inv.left ≫ E.hom.left ≫ a) hEV
      _ = EU.inv.left ≫ (A.ι ≫ eT.left) ≫ qY := by
        simpa only [Category.assoc] using
          congrArg (fun a => EU.inv.left ≫ a ≫ qY) hE
      _ = EU.inv.left ≫ A.ι ≫ (qX ≫ e.left) := by
        simpa only [Category.assoc] using
          congrArg (fun a => EU.inv.left ≫ A.ι ≫ a) he
      _ = (EU.inv.left ≫ (A.ι ≫ qX)) ≫ e.left := by
        simp only [Category.assoc]
      _ = (pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι) ≫ e.left :=
        congrArg (fun a => a ≫ e.left) hi
      _ = pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι ≫ e.left := Category.assoc _ _ _

/-- A Cartesian endpoint square over a composite base map factors through a
prescribed intermediate endpoint square, with both projections unchanged. -/
theorem factor_endpoint_square {B R T : Scheme.{u}} (ρ : R ⟶ B) (β : T ⟶ R)
    (C F : Over B) (CR FR : Over R) (CT FT : Over T)
    (qCR : CR.left ⟶ C.left) (qFR : FR.left ⟶ F.left)
    (hCR : IsPullback qCR CR.hom C.hom ρ)
    (hFR : IsPullback qFR FR.hom F.hom ρ)
    (e : C ⟶ F) (eR : CR ⟶ FR)
    (heR : eR.left ≫ qFR = qCR ≫ e.left)
    (qCT : CT.left ⟶ C.left) (qFT : FT.left ⟶ F.left)
    (hCT : IsPullback qCT CT.hom C.hom (β ≫ ρ))
    (hFT : IsPullback qFT FT.hom F.hom (β ≫ ρ))
    (eT : CT ⟶ FT) (heT : eT.left ≫ qFT = qCT ≫ e.left) :
    ∃ (qC : CT.left ⟶ CR.left) (qF : FT.left ⟶ FR.left),
      IsPullback qC CT.hom CR.hom β ∧ IsPullback qF FT.hom FR.hom β ∧
      eT.left ≫ qF = qC ≫ eR.left ∧ qC ≫ qCR = qCT ∧ qF ≫ qFR = qFT := by
  let qC := hCR.lift qCT (CT.hom ≫ β) (by rw [hCT.w, Category.assoc])
  let qF := hFR.lift qFT (FT.hom ≫ β) (by rw [hFT.w, Category.assoc])
  have hc : qC ≫ qCR = qCT := hCR.lift_fst _ _ _
  have hf : qF ≫ qFR = qFT := hFR.lift_fst _ _ _
  have hcb : qC ≫ CR.hom = CT.hom ≫ β := hCR.lift_snd _ _ _
  have hfb : qF ≫ FR.hom = FT.hom ≫ β := hFR.lift_snd _ _ _
  refine ⟨qC, qF, hCT.of_right' hCR, hFT.of_right' hFR, ?_, hc, hf⟩
  apply hFR.hom_ext
  · calc
      (eT.left ≫ qF) ≫ qFR = eT.left ≫ qFT :=
        (Category.assoc _ _ _).trans (congrArg (fun a => eT.left ≫ a) hf)
      _ = qCT ≫ e.left := heT
      _ = (qC ≫ qCR) ≫ e.left := congrArg (fun a => a ≫ e.left) hc.symm
      _ = qC ≫ (eR.left ≫ qFR) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => qC ≫ a) heR.symm)
      _ = (qC ≫ eR.left) ≫ qFR := (Category.assoc _ _ _).symm
  · calc
      (eT.left ≫ qF) ≫ FR.hom = eT.left ≫ (FT.hom ≫ β) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => eT.left ≫ a) hfb)
      _ = CT.hom ≫ β := (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ β) eT.w)
      _ = qC ≫ CR.hom := hcb.symm
      _ = (qC ≫ eR.left) ≫ FR.hom := by rw [Category.assoc, eR.w]

/-- A pointed isomorphism of scalar model opens determines a common open cell
in any Cartesian comparison of the two ambient models. -/
theorem exists_pointed_scalar_cell {B T : Scheme.{u}} (κ : T ⟶ B)
    (C F : Over B) (e : C ⟶ F) (U : C.left.Opens) (V : F.left.Opens)
    (E : Over.mk (pullback.fst κ (U.ι ≫ C.hom)) ≅
      Over.mk (pullback.fst κ (V.ι ≫ F.hom)))
    (hE : E.hom.left ≫ pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι =
      pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι ≫ e.left)
    (s : T ⟶ pullback κ (V.ι ≫ F.hom))
    (hs : s ≫ pullback.fst κ (V.ι ≫ F.hom) = 𝟙 T)
    (CT FT : Over T) (qC : CT.left ⟶ C.left) (qF : FT.left ⟶ F.left)
    (hC : IsPullback qC CT.hom C.hom κ)
    (hF : IsPullback qF FT.hom F.hom κ)
    (eT : CT ⟶ FT) (heT : eT.left ≫ qF = qC ≫ e.left) :
    ∃ (W : Over T) (c : W ⟶ CT) (j : W ⟶ FT),
      IsOpenImmersion c.left ∧ IsOpenImmersion j.left ∧ c ≫ eT = j ∧
      ∃ k : T ⟶ W.left, k ≫ W.hom = 𝟙 T := by
  let UA : Over T := Over.mk (pullback.fst κ (U.ι ≫ C.hom))
  let WB : Over T := Over.mk (pullback.fst κ (V.ι ≫ F.hom))
  let u0 : Over.mk (U.ι ≫ C.hom) ⟶ C := Over.homMk U.ι
  let v0 : Over.mk (V.ι ≫ F.hom) ⟶ F := Over.homMk V.ι
  let : IsOpenImmersion u0.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : IsOpenImmersion v0.left := inferInstanceAs (IsOpenImmersion V.ι)
  let u : UA ⟶ CT := Over.homMk
    (hC.lift (pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι) UA.hom
      ((Category.assoc _ _ _).trans pullback.condition.symm)) (hC.lift_snd _ _ _)
  let v : WB ⟶ FT := Over.homMk
    (hF.lift (pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι) WB.hom
      ((Category.assoc _ _ _).trans pullback.condition.symm)) (hF.lift_snd _ _ _)
  let : IsOpenImmersion u.left := lifted_cell_open κ _ C u0 CT qC hC
  let : IsOpenImmersion v.left := lifted_cell_open κ _ F v0 FT qF hF
  let c : WB ⟶ CT := E.inv ≫ u
  let : IsIso E.inv.left := by
    change IsIso ((Over.forget T).map E.inv)
    infer_instance
  let : IsOpenImmersion c.left :=
    inferInstanceAs (IsOpenImmersion (E.inv.left ≫ u.left))
  have hcinv : E.inv.left ≫
      (pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι ≫ e.left) =
      pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι :=
    inverse_projection ((Over.forget T).mapIso E) _ _ hE
  have hu : u.left ≫ qC = pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι :=
    hC.lift_fst _ _ _
  have hv : v.left ≫ qF = pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι :=
    hF.lift_fst _ _ _
  refine ⟨WB, c, v, inferInstance, inferInstance, ?_, s, hs⟩
  apply CostructuredArrow.hom_ext
  apply hF.hom_ext
  · change (E.inv.left ≫ u.left ≫ eT.left) ≫ qF = v.left ≫ qF
    calc
      (E.inv.left ≫ u.left ≫ eT.left) ≫ qF =
          E.inv.left ≫ u.left ≫ (qC ≫ e.left) := by
        simpa only [Category.assoc] using
          congrArg (fun a => E.inv.left ≫ u.left ≫ a) heT
      _ = E.inv.left ≫
          (pullback.snd κ (U.ι ≫ C.hom) ≫ U.ι ≫ e.left) := by
        simpa only [Category.assoc] using
          congrArg (fun a => E.inv.left ≫ a ≫ e.left) hu
      _ = pullback.snd κ (V.ι ≫ F.hom) ≫ V.ι := hcinv
      _ = v.left ≫ qF := hv.symm
  · exact (c ≫ eT).w.trans v.w.symm

end FrobeniusSplitting
