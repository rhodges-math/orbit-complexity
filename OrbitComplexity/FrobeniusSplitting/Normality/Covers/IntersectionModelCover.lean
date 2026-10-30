import OrbitComplexity.FrobeniusSplitting.Normality.ColimitModels
import OrbitComplexity.FrobeniusSplitting.Normality.DirectedSpectra
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionSquares
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Covers and smoothness of specified intersection models -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

@[implicit_reducible]
private def coconeCover {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    (F : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected] (c : Cocone F) (hc : IsColimit c) :
    c.pt.OpenCover.{u} := by
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hc
  have hleg (i : J) : colimit.ι F i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  refine { I₀ := J, X := F.obj, f := c.ι.app, mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨fun y ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨i, x, hx⟩ := (Scheme.IsLocallyDirected.openCover F).exists_eq (e.inv y)
    change J at i
    change F.obj i at x
    change (colimit.ι F i) x = e.inv y at hx
    refine ⟨i, x, ?_⟩
    have h := congrArg (fun f : F.obj i ⟶ c.pt ↦ f x) (hleg i)
    change e.hom ((colimit.ι F i) x) = (c.ι.app i) x at h
    exact h.symm.trans ((congrArg e.hom hx).trans
      (congrArg (fun f : c.pt ⟶ c.pt ↦ f y) e.inv_hom_id))
  · change IsOpenImmersion (c.ι.app i)
    rw [← hleg i]
    infer_instance

/-- Retained intersection pushouts give a smooth model with a cover after every base change. -/
theorem intersection_model_cover {X : Scheme.{u}} {I K R : Type u}
    [Finite I] [CommRing K] [CommRing R] [Algebra R K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ s, Algebra.FinitePresentation R (N.obj s)]
    [∀ s, Algebra.Smooth R (N.obj s)]
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] (intersectionCoordinates base (intersectionOpens U)).obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      ((intersectionCoordinates base (intersectionOpens U)).map f).hom.comp (e s).toAlgHom)
    (hopen : ∀ s t (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)))
    (hpush : ∀ s t r v (f : s ⟶ t) (g : s ⟶ r) (p : t ⟶ v) (q : r ⟶ v),
      IsPushout
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          f).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          g).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          p).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (N.map f).hom.toRingHom)
        (CommRingCat.ofHom (N.map g).hom.toRingHom)
        (CommRingCat.ofHom (N.map p).hom.toRingHom)
        (CommRingCat.ofHom (N.map q).hom.toRingHom)) :
    let cX := intersectionCoordinateCocone base U hU
    ∃ (cG : Cocone (N.op ⋙ algSpec (.of R))) (q : X ⟶ cG.pt.left),
      Nonempty (IsColimit cG) ∧
      IsPullback q base cG.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      (∀ s, (cX.ι.app s).left ≫ q =
        (affineModelNatTrans N (intersectionCoordinates base (intersectionOpens U)) e he).app s ≫
          (cG.ι.app s).left) ∧
      CompactSpace cG.pt.left ∧ LocallyOfFinitePresentation cG.pt.hom ∧
      Smooth cG.pt.hom ∧
      (∀ s, IsOpenImmersion (cG.ι.app s).left) ∧
      (∀ y : cG.pt.left, ∃ s x, (cG.ι.app s).left x = y) ∧
      ∀ (T : Scheme.{u}) (f : T ⟶ cG.pt.left) (y : T),
        ∃ s, ∃ z : (pullback f (cG.ι.app s).left : Scheme.{u}),
          (pullback.fst f (cG.ι.app s).left) z = y := by
  classical
  let F := intersectionCoordinates base (intersectionOpens U)
  let C := {s : Finset I // s.Nonempty}
  let (s t : C) (f : s ⟶ t) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)) := hopen s t f
  let : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := by
    apply specs_locallyDirected N
    intro s t r fi fj
    obtain ⟨v, gi, gj, hv⟩ :=
      intersectionCoordinates_refine base U hU (.op s) (.op t) (.op r) fi.op fj.op
    exact ⟨v.unop, gi.unop, gj.unop, hpush r s t v.unop fi fj gi.unop gj.unop hv⟩
  obtain ⟨cG, q, hG, hcart, hcomp, hcompact, hfp⟩ :=
    exists_affine_model_for_colimit N F e he
      (intersectionCoordinateCocone base U hU) (coordinateCoconeIsColimit base U hU hcover)
  let H := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let {s t : Cᵒᵖ} (f : s ⟶ t) : IsOpenImmersion (H.map f) :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let c := (Over.forget (Spec (.of R))).mapCocone cG
  let hc : IsColimit c := isColimitOfPreserves (Over.forget (Spec (.of R))) hG.some
  let 𝒱 := coconeCover H c hc
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  have hsmooth : Smooth cG.pt.hom := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u})
      (f := cG.pt.hom) 𝒱
    intro s
    change Cᵒᵖ at s
    change Smooth ((cG.ι.app s).left ≫ cG.pt.hom)
    have hw : (cG.ι.app s).left ≫ cG.pt.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s.unop))) :=
      Over.w (cG.ι.app s)
    rw [hw]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).2
      (RingHom.smooth_algebraMap.mpr inferInstance)
  refine ⟨cG, q, hG, hcart, hcomp, hcompact, hfp, hsmooth, ?_, ?_, ?_⟩
  · intro s
    exact 𝒱.map_prop s
  · intro y
    exact 𝒱.exists_eq y
  · intro T f y
    let 𝒲 : T.OpenCover.{u} := 𝒱.pullback₁ f
    exact 𝒲.exists_eq y

end FrobeniusSplitting
