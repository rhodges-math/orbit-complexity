import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartGluing

set_option autoImplicit false

/-! # Closed coordinate models inside a specified ambient colimit

The quotient transformation constructs the closed immersion. Its affine
colimit retains the prescribed scalar comparison, and colimit uniqueness
identifies its chart legs with the quotient gluing.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v w

private theorem transport_gluing {T : Type*} [Category T]
    {J : Type v} [Category.{w} J] {F G : J ⥤ T} (a : F ⟶ G)
    (c : Cocone F) (d : Cocone F) (b : Cocone G)
    (hc : IsColimit c) (hd : IsColimit d) (j : d.pt ⟶ b.pt)
    (hj : ∀ i, d.ι.app i ≫ j = a.app i ≫ b.ι.app i) :
    ∀ i, c.ι.app i ≫ (hc.coconePointUniqueUpToIso hd).hom ≫ j =
      a.app i ≫ b.ι.app i := by
  intro i
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ j) (hc.comp_coconePointUniqueUpToIso_hom hd i))).trans (hj i)

private theorem glued_comparison {T : Type*} [Category T]
    {J : Type v} [Category.{w} J] {BN FN BM FM : J ⥤ T}
    (aB : BN ⟶ BM) (aF : FN ⟶ FM) (bN : BN ⟶ FN) (bM : BM ⟶ FM)
    (cBN : Cocone BN) (cFN : Cocone FN) (cBM : Cocone BM) (cFM : Cocone FM)
    (hcBN : IsColimit cBN) (qB : cBN.pt ⟶ cBM.pt) (qF : cFN.pt ⟶ cFM.pt)
    (jN : cBN.pt ⟶ cFN.pt) (jM : cBM.pt ⟶ cFM.pt)
    (hqB : ∀ i, cBN.ι.app i ≫ qB = aB.app i ≫ cBM.ι.app i)
    (hqF : ∀ i, cFN.ι.app i ≫ qF = aF.app i ≫ cFM.ι.app i)
    (hjN : ∀ i, cBN.ι.app i ≫ jN = bN.app i ≫ cFN.ι.app i)
    (hjM : ∀ i, cBM.ι.app i ≫ jM = bM.app i ≫ cFM.ι.app i)
    (hsquare : ∀ i, aB.app i ≫ bM.app i = bN.app i ≫ aF.app i) :
    qB ≫ jM = jN ≫ qF := by
  apply hcBN.hom_ext
  intro i
  calc
    cBN.ι.app i ≫ (qB ≫ jM) = (aB.app i ≫ cBM.ι.app i) ≫ jM :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ jM) (hqB i))
    _ = aB.app i ≫ (bM.app i ≫ cFM.ι.app i) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => aB.app i ≫ f) (hjM i))
    _ = (bN.app i ≫ aF.app i) ≫ cFM.ι.app i :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ cFM.ι.app i) (hsquare i))
    _ = bN.app i ≫ (cFN.ι.app i ≫ qF) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => bN.app i ≫ f) (hqF i).symm)
    _ = cBN.ι.app i ≫ (jN ≫ qF) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ qF) (hjN i).symm).trans (Category.assoc _ _ _))

private theorem inclusion_over {R : Scheme.{u}} {J : Type v} [Category.{w} J]
    (F G : J ⥤ Over R) (a : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (hcF : IsColimit ((Over.forget R).mapCocone cF))
    (j : cF.pt.left ⟶ cG.pt.left)
    (hj : ∀ i, (cF.ι.app i).left ≫ j = (a.app i).left ≫ (cG.ι.app i).left) :
    j ≫ cG.pt.hom = cF.pt.hom := by
  apply hcF.hom_ext
  intro i
  calc
    (cF.ι.app i).left ≫ (j ≫ cG.pt.hom) =
        ((a.app i).left ≫ (cG.ι.app i).left) ≫ cG.pt.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ cG.pt.hom) (hj i))
    _ = (a.app i).left ≫ (G.obj i).hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => (a.app i).left ≫ f) (cG.ι.app i).w)
    _ = (F.obj i).hom := (a.app i).w
    _ = (cF.ι.app i).left ≫ cF.pt.hom := (cF.ι.app i).w.symm

/-- The specified quotient atlas constructs a closed model inside its
specified ambient colimit. The scalar comparison, all quotient chart legs
and the prescribed inclusion of the original schemes are preserved. -/
theorem exists_closed_model_in_atlas
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] [Finite C]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (F₀ B₀ : C ⥤ CommAlgCat.{u} R) (F B : C ⥤ CommAlgCat.{u} K)
    (eF : ∀ i, K ⊗[R] F₀.obj i ≃ₐ[K] F.obj i)
    (eB : ∀ i, K ⊗[R] B₀.obj i ≃ₐ[K] B.obj i)
    [∀ i, Algebra.FinitePresentation R (B₀.obj i)]
    (hF : ∀ i j (f : i ⟶ j), (eF j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map f).hom) =
      (F.map f).hom.comp (eF i).toAlgHom)
    (hB : ∀ i j (f : i ⟶ j), (eB j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (B₀.map f).hom) =
      (B.map f).hom.comp (eB i).toAlgHom)
    (β₀ : F₀ ⟶ B₀) (β : F ⟶ B)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F₀.map f).hom.toRingHom))]
    [((F₀.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (hcart : (Functor.whiskerRight (NatTrans.op β₀)
      (algSpec (.of R) ⋙ Over.forget _)).Equifibered)
    (hclosed : ∀ i, IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (β₀.app i).hom.toRingHom)))
    (cFN : Cocone (F.op ⋙ algSpec (.of K)))
    (cBN : Cocone (B.op ⋙ algSpec (.of K))) (hcBN : IsColimit cBN)
    (cFM : Cocone (F₀.op ⋙ algSpec (.of R))) (hcFM : IsColimit cFM)
    (qF : cFN.pt.left ⟶ cFM.pt.left)
    (hqF : ∀ i, (cFN.ι.app i).left ≫ qF =
      (affineModelNatTrans F₀ F eF hF).app i ≫ (cFM.ι.app i).left)
    (jN : cBN.pt ⟶ cFN.pt)
    (hjN : ∀ i, cBN.ι.app i ≫ jN =
      (algSpec (.of K)).map (β.app i.unop).op ≫ cFN.ι.app i)
    (hsquare : ∀ i,
      (affineModelNatTrans B₀ B eB hB).app i ≫
        ((algSpec (.of R)).map (β₀.app i.unop).op).left =
      ((algSpec (.of K)).map (β.app i.unop).op).left ≫
        (affineModelNatTrans F₀ F eF hF).app i) :
    ∃ (cBM : Cocone (B₀.op ⋙ algSpec (.of R)))
      (qB : cBN.pt.left ⟶ cBM.pt.left) (jM : cBM.pt ⟶ cFM.pt),
      Nonempty (IsColimit cBM) ∧ IsClosedImmersion jM.left ∧
      IsPullback qB cBN.pt.hom cBM.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      (∀ i, (cBN.ι.app i).left ≫ qB =
        (affineModelNatTrans B₀ B eB hB).app i ≫ (cBM.ι.app i).left) ∧
      (∀ i, (cBM.ι.app i).left ≫ jM.left =
        ((algSpec (.of R)).map (β₀.app i.unop).op).left ≫ (cFM.ι.app i).left) ∧
      qB ≫ jM.left = jN.left ≫ qF ∧
      CompactSpace cBM.pt.left ∧ LocallyOfFinitePresentation cBM.pt.hom := by
  let FM := F₀.op ⋙ algSpec (.of R)
  let BM := B₀.op ⋙ algSpec (.of R)
  let aM : BM ⟶ FM := Functor.whiskerRight (NatTrans.op β₀) (algSpec (.of R))
  let aMS := Functor.whiskerRight aM (Over.forget (Spec (.of R)))
  let {i j} (f : i ⟶ j) : IsOpenImmersion ((FM ⋙ Over.forget _).map f) :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F₀.map f.unop).hom.toRingHom)))
  let {i j} (f : i ⟶ j) : IsOpenImmersion ((BM ⋙ Over.forget _).map f) :=
    MorphismProperty.of_isPullback (hcart f).flip
      (inferInstanceAs (IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (F₀.map f.unop).hom.toRingHom))))
  let {i j} (f : i ⟶ j) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (B₀.map f).hom.toRingHom)) := by
    exact inferInstanceAs (IsOpenImmersion ((BM ⋙ Over.forget _).map f.op))
  let : ((FM ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected :=
    inferInstanceAs
      (((F₀.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected)
  let : ((BM ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective aMS hcart
      (fun f => (((BM ⋙ Over.forget _).map f)).injective)
  let : ((B₀.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected :=
    inferInstanceAs (((BM ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected)
  obtain ⟨cBM, qB, hcBM, hqB, hlegsB, hcompact, hfp⟩ :=
    exists_affine_model_for_colimit B₀ B eB hB cBN hcBN
  let hcBMS := isColimitOfPreserves (Over.forget (Spec (.of R))) hcBM.some
  let hcFMS := isColimitOfPreserves (Over.forget (Spec (.of R))) hcFM
  obtain ⟨c, j, hc, hj, hlegs⟩ := exists_closed_atlas_gluing
    (BM ⋙ Over.forget _) (FM ⋙ Over.forget _) aMS hcart
    ((Over.forget _).mapCocone cFM) hcFMS (fun i => hclosed i.unop)
  let E := hcBMS.coconePointUniqueUpToIso hc.some
  let m := E.hom ≫ j
  have hm (i) : (cBM.ι.app i).left ≫ m =
      (aM.app i).left ≫ (cFM.ι.app i).left :=
    transport_gluing aMS ((Over.forget _).mapCocone cBM) c
      ((Over.forget _).mapCocone cFM) hcBMS hc.some j hlegs i
  let : IsClosedImmersion j := hj
  let jM : cBM.pt ⟶ cFM.pt := Over.homMk m (inclusion_over BM FM aM cBM cFM hcBMS m hm)
  have hjM : IsClosedImmersion jM.left := inferInstanceAs (IsClosedImmersion (E.hom ≫ j))
  have hcomparison : qB ≫ jM.left = jN.left ≫ qF :=
    glued_comparison (affineModelNatTrans B₀ B eB hB)
      (affineModelNatTrans F₀ F eF hF)
      (Functor.whiskerRight (NatTrans.op β) (algSpec (.of K) ⋙ Over.forget _)) aMS
      ((Over.forget _).mapCocone cBN) ((Over.forget _).mapCocone cFN)
      ((Over.forget _).mapCocone cBM) ((Over.forget _).mapCocone cFM)
      (isColimitOfPreserves (Over.forget _) hcBN) qB qF jN.left jM.left
      hlegsB hqF (fun i => congrArg (fun f => f.left) (hjN i)) hm hsquare
  exact ⟨cBM, qB, jM, hcBM, hjM, hqB, hlegsB, hm, hcomparison, hcompact, hfp⟩

end SchubertGeometry
