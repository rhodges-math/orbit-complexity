import OrbitComplexity.SchubertGeometry.Normality.LongestBirationalStage
import OrbitComplexity.SchubertGeometry.Connectedness.SmoothFlagStage
import OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarArrowSquares
import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected
import OrbitComplexity.FrobeniusSplitting.Normality.ProperPushforward
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralSource
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Common coefficient stages for flag pushforward

Smoothness of the flag model, connectedness of the longest-word endpoint and
birationality hold at one coefficient stage. A proper smooth geometrically
connected word model gives integral source fibres; the endpoint then induces
an isomorphism of structure sheaves on every field fibre.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

namespace SchubertGeometry

universe u

open private comparison_at_stage from
  OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource
open private endpoint_from_projections from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.BirationalSchemeStages
open private spec_triangle from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

private theorem smooth_composite_fibre {B R T : Scheme.{u}}
    (ρ : R ⟶ B) (β : T ⟶ R) (F : Over B) (FR : Over R) (FT : Over T)
    (qR : FR.left ⟶ F.left) (hR : IsPullback qR FR.hom F.hom ρ)
    (qT : FT.left ⟶ F.left) (hT : IsPullback qT FT.hom F.hom (β ≫ ρ))
    (hs : Smooth FR.hom) : Smooth FT.hom :=
  MorphismProperty.of_isPullback (P := @Smooth) (hT.of_right' hR) hs

private theorem endpoint_fibre_connected {B R T : Scheme.{u}}
    (ρ : R ⟶ B) (β : T ⟶ R) (C F : Over B) (CL FL : Over T)
    (e : C ⟶ F) (eL : CL ⟶ FL)
    (qCL : CL.left ⟶ C.left) (qFL : FL.left ⟶ F.left)
    (hCL : IsPullback qCL CL.hom C.hom (β ≫ ρ))
    (hFL : IsPullback qFL FL.hom F.hom (β ≫ ρ))
    (he : eL.left ≫ qFL = qCL ≫ e.left)
    (hgc : GeometricallyConnected (chosenScalarArrow ρ e).left) :
    GeometricallyConnected eL.left := by
  have hC : IsPullback (pullback.snd ρ C.hom)
      (pullback.fst ρ C.hom) C.hom ρ :=
    (IsPullback.of_hasPullback ρ C.hom).flip
  have hF : IsPullback (pullback.snd ρ F.hom)
      (pullback.fst ρ F.hom) F.hom ρ :=
    (IsPullback.of_hasPullback ρ F.hom).flip
  let qC := hC.lift qCL (CL.hom ≫ β) (hCL.w.trans (Category.assoc _ _ _).symm)
  let qF := hF.lift qFL (FL.hom ≫ β) (hFL.w.trans (Category.assoc _ _ _).symm)
  have hC_old : qC ≫ pullback.snd ρ C.hom = qCL := hC.lift_fst _ _ _
  have hC_base : qC ≫ pullback.fst ρ C.hom = CL.hom ≫ β := hC.lift_snd _ _ _
  have hF_old : qF ≫ pullback.snd ρ F.hom = qFL := hF.lift_fst _ _ _
  have hF_base : qF ≫ pullback.fst ρ F.hom = FL.hom ≫ β := hF.lift_snd _ _ _
  have hOuter : IsPullback qCL (eL.left ≫ FL.hom) (e.left ≫ F.hom) (β ≫ ρ) := by
    simpa only [eL.w, e.w] using hCL
  have hEndpoint : IsPullback eL.left qCL qFL e.left :=
    (hOuter.of_bot he.symm hFL).flip
  have hSquare : eL.left ≫ qF = qC ≫ (chosenScalarArrow ρ e).left := by
    apply hF.hom_ext
    · calc
        (eL.left ≫ qF) ≫ pullback.snd ρ F.hom = eL.left ≫ qFL := by
          rw [Category.assoc, hF_old]
        _ = qCL ≫ e.left := he
        _ = (qC ≫ pullback.snd ρ C.hom) ≫ e.left :=
          congrArg (fun a => a ≫ e.left) hC_old.symm
        _ = (qC ≫ (chosenScalarArrow ρ e).left) ≫ pullback.snd ρ F.hom := by
          simpa only [Category.assoc] using
            congrArg (fun a => qC ≫ a) (chosenScalarArrow_snd ρ e).symm
    · calc
        (eL.left ≫ qF) ≫ pullback.fst ρ F.hom = eL.left ≫ (FL.hom ≫ β) := by
          rw [Category.assoc, hF_base]
        _ = CL.hom ≫ β := by rw [← Category.assoc, eL.w]
        _ = qC ≫ pullback.fst ρ C.hom := hC_base.symm
        _ = (qC ≫ (chosenScalarArrow ρ e).left) ≫ pullback.fst ρ F.hom := by
          have hbase : (chosenScalarArrow ρ e).left ≫ pullback.fst ρ F.hom =
              pullback.fst ρ C.hom := (chosenScalarArrow ρ e).w
          exact (congrArg (fun a => qC ≫ a) hbase).symm.trans
            (Category.assoc _ _ _).symm
  have hOuter' : IsPullback eL.left (qC ≫ pullback.snd ρ C.hom)
      (qF ≫ pullback.snd ρ F.hom) e.left := by
    rw [hC_old, hF_old]
    exact hEndpoint
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    ((hOuter'.of_bot hSquare (chosenScalarArrow_cartesian ρ e)).flip) hgc

private theorem sheaf_iso_of_normal_stalks {X Y : Scheme.{u}}
    [IrreducibleSpace Y] (f : X ⟶ Y)
    (hb : Scheme.BirationalOver f (𝟙 Y))
    (hn : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hX : IsIntegral X) (hf : IsProper f) : IsIso f.c := by
  let : IsIntegral X := hX
  let : IsProper f := hf
  let : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    let : IsDomain (Y.presheaf.stalk y) := (hn y).1
    infer_instance
  let : IsReduced Y := isReduced_of_isReduced_stalk Y
  let : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  exact proper_birational_sheaf f hb (fun y => (hn y).2)

/-- A proper smooth geometrically connected word model has integral field
fibres, and its longest-word endpoint has an isomorphic structure sheaf on
every field fibre after one coefficient extension. -/
theorem exists_flag_pushforward_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement)
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
    [IsSeparated F.hom]
    [QuasiSeparatedSpace C.left] [QuasiSeparatedSpace F.left]
    [CompactSpace F.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (e : C ⟶ F) (qC : bsdhScheme G word ⟶ C.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = bsdhMap G word ≫ qF) (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      Smooth (stageScalarModel S F.hom t).hom ∧
      GeometricallyConnected (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) e).left ∧
      ∃ (qtC : bsdhScheme G word ⟶ (stageScalarModel S C.hom t).left)
        (qtF : (flagVariety G).scheme ⟶ (stageScalarModel S F.hom t).left),
        IsPullback qtC (bsdhToSpec G word) (stageScalarModel S C.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback qtF (flagVariety G).toSpec (stageScalarModel S F.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qtC ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) C.hom = qC
              ∧
        qtF ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) F.hom = qF
              ∧
        qtC ≫ (chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) e).left =
          bsdhMap G word ≫ qtF ∧
        ∀ (L : Type u) [Field L] [Algebra t.val L]
          (CL FL : Over (Spec (.of L)))
          (qCL : CL.left ⟶ C.left) (qFL : FL.left ⟶ F.left)
          (_hCL : IsPullback qCL CL.hom C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
              Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
          (_hFL : IsPullback qFL FL.hom F.hom
            (Spec.map (CommRingCat.ofHom (algebraMap t.val L)) ≫
              Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
          (eL : CL ⟶ FL) (_heL : eL.left ≫ qFL = qCL ≫ e.left),
          IsIntegral CL.left ∧ GeometricallyConnected eL.left ∧ IsProper eL.left ∧
          Smooth FL.hom ∧
          (∀ y : FL.left, IsDomain (FL.left.presheaf.stalk y) ∧
            IsIntegrallyClosed (FL.left.presheaf.stalk y)) ∧
          Scheme.BirationalOver eL.left (𝟙 FL.left) ∧
          IsIso eL.left.c := by
  obtain ⟨r, hstart, hs, _, _⟩ := exists_smooth_flag_stage G S hS F qF hF start
  let : IsProper (e.left ≫ F.hom) := by rw [e.w]; infer_instance
  let : IsProper e.left := IsProper.of_comp e.left F.hom
  have hi : IsIso (schubertInclusion G (simpleWeylWord G.rootBase word)).left := by
    rw [hw]
    exact inferInstanceAs (IsIso
      ((Over.forget (Spec (.of K))).mapIso (longestSchubertIso G)).hom)
  let : IsIso (schubertInclusion G (simpleWeylWord G.rootBase word)).left := hi
  let qD := (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qF
  have hInclusion : IsPullback
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left
      (schubertVariety G (simpleWeylWord G.rootBase word)).toSpec
      (flagVariety G).toSpec (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨(schubertInclusion G _).w.trans (Category.comp_id _).symm⟩
  have hD : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase word)).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
    simpa only [Category.id_comp] using hInclusion.paste_horiz hF
  have heD : qC ≫ e.left = (bsdhSchubertMap G word hred).left ≫ qD := by
    change qC ≫ e.left = (bsdhSchubertMap G word hred).left ≫
      ((schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qF)
    rw [← Category.assoc, bsdhSchubertMap_comp G word hred]
    exact he
  have hjD : qD ≫ (𝟙 F : F ⟶ F).left =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qF :=
    Category.comp_id _
  obtain ⟨k, hrk, hgc, _hproper, _hbase, _hold, _hfields, _hretained⟩ :=
    @exists_word_endpoint_connected.{u} K inferInstance inferInstance inferInstance
      G word hred S hS F inferInstance inferInstance inferInstance qF hF C F e (𝟙 F)
      inferInstance inferInstance qC qD hC hD heD hjD r
  obtain ⟨t, hrt, hb⟩ := exists_longest_birational_stage G word hred hw
    S hS C F e qC qF hC hF he k
  have hst : Smooth (stageScalarModel S F.hom t).hom :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (stageScalarCartesian S F.hom (hrk.trans hrt)) hs
  obtain ⟨qtC, hqtC, hCt⟩ := @comparison_at_stage.{u} K inferInstance S C.left C.hom t
    (Over.mk (bsdhToSpec G word)) qC hC
  obtain ⟨qtF, hqtF, hFt⟩ := @comparison_at_stage.{u} K inferInstance S F.left F.hom t (flagVariety
    G).toOver qF hF
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap t.val K))
  let Ct := stageScalarModel S C.hom t
  let Ft := stageScalarModel S F.hom t
  let et : Ct ⟶ Ft := chosenScalarArrow ρ e
  have hcoefficient :
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrt).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom) = ρ :=
    spec_triangle (Subalgebra.inclusion k.property.2).toRingHom
      (Subalgebra.inclusion hrt).toRingHom (Subalgebra.inclusion t.property.2).toRingHom
      (by ext a; rfl)
  have hCscalar : IsPullback (pullback.snd ρ C.hom) Ct.hom C.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrt).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) := by
    rw [hcoefficient]
    exact (IsPullback.of_hasPullback ρ C.hom).flip
  have hFscalar : IsPullback (pullback.snd ρ F.hom) Ft.hom F.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrt).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) := by
    rw [hcoefficient]
    exact (IsPullback.of_hasPullback ρ F.hom).flip
  have hgcT : GeometricallyConnected et.left :=
    endpoint_fibre_connected
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrt).toRingHom)) C F Ct Ft e et
      (pullback.snd ρ C.hom) (pullback.snd ρ F.hom) hCscalar hFscalar
      (chosenScalarArrow_snd ρ e) hgc
  let CN : Over (Spec (.of K)) := Over.mk (bsdhToSpec G word)
  let FN := (flagVariety G).toOver
  let eN : CN ⟶ FN := Over.homMk (bsdhMap G word) rfl
  have hcartF : IsPullback (pullback.snd ρ F.hom) Ft.hom F.hom ρ :=
    (IsPullback.of_hasPullback ρ F.hom).flip
  have hendpoint : eN.left ≫ qtF = qtC ≫ et.left :=
    endpoint_from_projections ρ κ C F Ct Ft CN FN
      (pullback.snd ρ C.hom) (pullback.snd ρ F.hom) hcartF e et
      (chosenScalarArrow_snd ρ e) qC qF qtC qtF hCt hFt hqtC.w hqtF.w eN he.symm
  refine ⟨t, hstart.trans (hrk.trans hrt), hst, hgcT,
    qtC, qtF, hqtC, hqtF, hCt, hFt, hendpoint.symm, ?_⟩
  intro L _ _ CL FL qCL qFL hCL hFL eL heL
  let : IsProper CL.hom := MorphismProperty.of_isPullback (P := @IsProper) hCL inferInstance
  let : Smooth CL.hom := MorphismProperty.of_isPullback (P := @Smooth) hCL inferInstance
  let : GeometricallyConnected CL.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hCL inferInstance
  let : IsLocallyNoetherian CL.left := LocallyOfFiniteType.isLocallyNoetherian CL.hom
  have hI : IsIntegral CL.left :=
    isIntegral_of_proper CL.hom fun x => (stalks_of_smooth CL.hom x).1
  let : IsIntegral CL.left := hI
  have hgcL : GeometricallyConnected eL.left :=
    endpoint_fibre_connected ρ
      (Spec.map (CommRingCat.ofHom (algebraMap t.val L))) C F CL FL e eL
      qCL qFL hCL hFL heL hgcT
  let : GeometricallyConnected eL.left := hgcL
  let : IrreducibleSpace FL.left :=
    Function.Surjective.irreducibleSpace eL.left.continuous eL.left.surjective
  let : IsSeparated FL.hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hFL inferInstance
  let : IsProper (eL.left ≫ FL.hom) := by rw [eL.w]; infer_instance
  have hproperL : IsProper eL.left := IsProper.of_comp eL.left FL.hom
  have hbL := hb L CL FL qCL qFL hCL hFL eL heL
  let β := Spec.map (CommRingCat.ofHom (algebraMap t.val L))
  have hsm : Smooth FL.hom :=
    smooth_composite_fibre ρ β F Ft FL (pullback.snd ρ F.hom) hcartF qFL hFL hst
  let : Smooth FL.hom := hsm
  have hn := stalks_of_smooth FL.hom
  exact ⟨hI, hgcL, hproperL, hsm, hn, hbL,
    sheaf_iso_of_normal_stalks eL.left hbL hn hI hproperL⟩

end SchubertGeometry
