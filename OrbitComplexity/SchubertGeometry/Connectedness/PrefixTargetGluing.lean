import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixAtlasGluing
import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

set_option autoImplicit false

/-! # Closed prefix targets on a specified ambient coefficient model

The coordinate atlases are glued first. One retained ambient isomorphism
then places all of their closed targets in the specified ambient model.
The comparison with each original closed scheme and both coefficient
projections are preserved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

open private scalar_comparison cone_original original_triangle
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage

private theorem quotient_comparison {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {M N : CommAlgCat.{u} R} {A B : CommAlgCat.{u} K}
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (f₀ : M ⟶ N) (f : A ⟶ B)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f₀.hom) =
      f.hom.comp eM.toAlgHom)
    (qM : Spec (.of A) ⟶ Spec (.of M)) (qN : Spec (.of B) ⟶ Spec (.of N))
    (hM : qM = Spec.map (CommRingCat.ofHom
      (eM.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
    (hN : qN = Spec.map (CommRingCat.ofHom
      (eN.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) :
    qN ≫ Spec.map (CommRingCat.ofHom f₀.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ qM := by
  subst qM
  subst qN
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro m
  have hm := AlgHom.congr_fun hf ((1 : K) ⊗ₜ[R] m)
  change eN ((1 : K) ⊗ₜ[R] f₀.hom m) = f.hom (eM ((1 : K) ⊗ₜ[R] m)) at hm
  exact hm

private theorem ambient_triangle {B : Scheme.{u}} {N G P : Over B}
    (EG : N ≅ G) (EP : N ≅ P) (E : G ≅ P) (hE : E = EG.symm ≪≫ EP)
    {X Y : Scheme.{u}} (p : G.left ⟶ X) (q : P.left ⟶ Y) (f : X ⟶ Y)
    (h : p ≫ f = E.hom.left ≫ q) :
    (EG.hom.left ≫ p) ≫ f = EP.hom.left ≫ q := by
  have he : EG.hom ≫ E.hom = EP.hom := by
    subst E
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have hel : EG.hom.left ≫ E.hom.left = EP.hom.left := congrArg (fun a => a.left) he
  calc
    (EG.hom.left ≫ p) ≫ f = EG.hom.left ≫ (E.hom.left ≫ q) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => EG.hom.left ≫ a) h)
    _ = EP.hom.left ≫ q :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ q) hel)

private theorem stage_properties {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (hS : S.FG) (X : Over (Spec (.of S))) [CompactSpace X.left]
    [LocallyOfFinitePresentation X.hom] (k : CoefficientStage S) :
    LocallyOfFinitePresentation (stageScalarModel S X.hom k).hom ∧
      CompactSpace (stageScalarModel S X.hom k).left ∧
      QuasiSeparatedSpace (stageScalarModel S X.hom k).left := by
  let : IsNoetherianRing S := isNoetherianRing_of_fg hS
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : AlgebraicGeometry.IsNoetherian X.left := AlgebraicGeometry.IsNoetherian.mk
  let : QuasiCompact X.hom := inferInstance
  let : IsNoetherianRing k.val := isNoetherianRing_of_fg k.property.1
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let : LocallyOfFinitePresentation (stageScalarModel S X.hom k).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ X.hom))
  let : QuasiCompact (stageScalarModel S X.hom k).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst κ X.hom))
  let : CompactSpace (stageScalarModel S X.hom k).left :=
    QuasiCompact.compactSpace_of_compactSpace (stageScalarModel S X.hom k).hom
  let : IsLocallyNoetherian (stageScalarModel S X.hom k).left :=
    LocallyOfFiniteType.isLocallyNoetherian (stageScalarModel S X.hom k).hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem scalar_closed {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (chosenScalarArrow κ f).left := by
  have h : IsPullback (chosenScalarArrow κ f).left (pullback.snd κ X.hom)
      (pullback.snd κ Y.hom) f.left := by
    have hout : IsPullback ((chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom)
        (pullback.snd κ X.hom) κ (f.left ≫ Y.hom) := by
      have hw : (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
          pullback.fst κ X.hom := (chosenScalarArrow κ f).w
      rw [hw, f.w]
      exact IsPullback.of_hasPullback κ X.hom
    exact hout.of_right (chosenScalarArrow_snd κ f) (IsPullback.of_hasPullback κ Y.hom)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip inferInstance

private theorem closed_over_iso {T : Scheme.{u}} {X Y : Over T} (E : X ≅ Y) :
    IsClosedImmersion E.hom.left := by
  let : IsIso E.hom.left := inferInstanceAs (IsIso ((Over.forget T).map E.hom))
  infer_instance

private theorem closed_comp_iso {T : Scheme.{u}} {X Y Z : Over T}
    (f : X ⟶ Y) (E : Y ≅ Z) (hf : IsClosedImmersion f.left) :
    IsClosedImmersion (f ≫ E.hom).left := by
  let : IsClosedImmersion f.left := hf
  let : IsClosedImmersion E.hom.left := closed_over_iso E
  exact IsClosedImmersion.comp f.left E.hom.left

private theorem target_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {N T : Over (Spec (.of K))} {B G P : Over (Spec (.of S))}
    [CompactSpace B.left] [LocallyOfFinitePresentation B.hom]
    (qB : N.left ⟶ B.left) (qG : T.left ⟶ G.left)
    (hB : IsPullback qB N.hom B.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hG : IsPullback qG T.hom G.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (j : B ⟶ G) [IsClosedImmersion j.left] (jN : N ⟶ T)
    (hj : qB ≫ j.left = jN.left ≫ qG) (k : CoefficientStage S)
    (EG : T ≅ genericScalarModel S G.hom) (EP : T ≅ genericScalarModel S P.hom)
    (hEG : EG = hG.flip.isoOverPullback)
    (E : genericScalarModel S G.hom ≅ genericScalarModel S P.hom)
    (hE : E = EG.symm ≪≫ EP)
    (Ek : stageScalarModel S G.hom k ≅ stageScalarModel S P.hom k)
    (hEk : (modelScalarCone S G.hom).π.app (op k) ≫ Ek.hom.left =
      E.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)) :
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    let EB : N ≅ genericScalarModel S B.hom := hB.flip.isoOverPullback
    let qBk := EB.hom.left ≫ (modelScalarCone S B.hom).π.app (op k)
    let qPk := EP.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)
    let jk := chosenScalarArrow κ j ≫ Ek.hom
    IsClosedImmersion jk.left ∧
      IsPullback qBk N.hom (stageScalarModel S B.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qBk ≫ jk.left = jN.left ≫ qPk ∧
      qBk ≫ pullback.snd κ B.hom = qB ∧
      LocallyOfFinitePresentation (stageScalarModel S B.hom k).hom ∧
      CompactSpace (stageScalarModel S B.hom k).left ∧
      QuasiSeparatedSpace (stageScalarModel S B.hom k).left := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let EB : N ≅ genericScalarModel S B.hom := hB.flip.isoOverPullback
  let qBk := EB.hom.left ≫ (modelScalarCone S B.hom).π.app (op k)
  let qGk := EG.hom.left ≫ (modelScalarCone S G.hom).π.app (op k)
  let qPk := EP.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)
  have hBk := overIso_modelStage_cartesian S B.hom k N EB
  have hGk := overIso_modelStage_cartesian S G.hom k T EG
  have hBo : qBk ≫ pullback.snd κ B.hom = qB :=
    original_triangle EB.hom.left _ _ _ qB (cone_original S B k)
      hB.flip.isoOverPullback_hom_left_comp_snd
  have hGo : qGk ≫ pullback.snd κ G.hom = qG := by
    subst EG
    exact original_triangle _ _ _ _ qG (cone_original S G k)
      hG.flip.isoOverPullback_hom_left_comp_snd
  have hscalar : qBk ≫ (chosenScalarArrow κ j).left = jN.left ≫ qGk :=
    scalar_comparison κ ρ j jN qB qG qBk qGk hBk hGk hBo hGo hj
  have hambient : qGk ≫ Ek.hom.left = qPk :=
    ambient_triangle EG EP E hE _ _ _ hEk
  have hclosed : IsClosedImmersion (chosenScalarArrow κ j ≫ Ek.hom).left :=
    closed_comp_iso (chosenScalarArrow κ j) Ek (scalar_closed κ j)
  have hinclusion : qBk ≫ (chosenScalarArrow κ j ≫ Ek.hom).left = jN.left ≫ qPk := by
    change qBk ≫ ((chosenScalarArrow κ j).left ≫ Ek.hom.left) = jN.left ≫ qPk
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ Ek.hom.left) hscalar).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => jN.left ≫ f) hambient)))
  have hprops := stage_properties S hS B k
  exact ⟨hclosed, hBk, hinclusion, hBo, hprops.1, hprops.2.1, hprops.2.2⟩

private def target_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {C : Type u} [Category.{u} C] {I : Type v}
    (F₀ : C ⥤ CommAlgCat.{u} S) (B₀ : I → C ⥤ CommAlgCat.{u} S)
    (β₀ : ∀ i, F₀ ⟶ B₀ i)
    (F : C ⥤ CommAlgCat.{u} K) (B : I → C ⥤ CommAlgCat.{u} K)
    (eF : ∀ c, K ⊗[S] F₀.obj c ≃ₐ[K] F.obj c)
    (eB : ∀ i c, K ⊗[S] (B₀ i).obj c ≃ₐ[K] (B i).obj c)
    (hF : ∀ c d (f : c ⟶ d), (eF d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map f).hom) =
      (F.map f).hom.comp (eF c).toAlgHom)
    (hB : ∀ i c d (f : c ⟶ d), (eB i d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map f).hom) =
      ((B i).map f).hom.comp (eB i c).toAlgHom)
    (cFN : Cocone (F.op ⋙ algSpec (.of K)))
    (cBN : ∀ i, Cocone ((B i).op ⋙ algSpec (.of K)))
    (jN : ∀ i, (cBN i).pt ⟶ cFN.pt)
    (P : Over (Spec (.of S))) (qP : cFN.pt.left ⟶ P.left)
    (hP : IsPullback qP cFN.pt.hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S) : Prop :=
  ∃ (cFM : Cocone (F₀.op ⋙ algSpec (.of S)))
    (cBM : ∀ i, Cocone ((B₀ i).op ⋙ algSpec (.of S)))
    (qF : cFN.pt.left ⟶ cFM.pt.left) (qB : ∀ i, (cBN i).pt.left ⟶ (cBM i).pt.left)
    (jM : ∀ i, (cBM i).pt ⟶ cFM.pt),
    Nonempty (IsColimit cFM) ∧ (∀ i, Nonempty (IsColimit (cBM i))) ∧
    (∀ i, IsClosedImmersion (jM i).left) ∧
    ∃ hqF : IsPullback qF cFN.pt.hom cFM.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))),
    (∀ i, IsPullback (qB i) (cBN i).pt.hom (cBM i).pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) ∧
    (∀ c, (cFN.ι.app c).left ≫ qF =
      (affineModelNatTrans F₀ F eF hF).app c ≫ (cFM.ι.app c).left) ∧
    (∀ i c, ((cBN i).ι.app c).left ≫ qB i =
      (affineModelNatTrans (B₀ i) (B i) (eB i) (hB i)).app c ≫ ((cBM i).ι.app c).left) ∧
    (∀ i c, ((cBM i).ι.app c).left ≫ (jM i).left =
      ((algSpec (.of S)).map ((β₀ i).app c.unop).op).left ≫ (cFM.ι.app c).left) ∧
    (∀ i, qB i ≫ (jM i).left = (jN i).left ≫ qF) ∧
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (Ek : stageScalarModel S cFM.pt.hom k ≅ stageScalarModel S P.hom k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let EG : cFN.pt ≅ genericScalarModel S cFM.pt.hom := hqF.flip.isoOverPullback
      let EP : cFN.pt ≅ genericScalarModel S P.hom := hP.flip.isoOverPullback
      let qPk := EP.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)
      ((modelScalarCone S cFM.pt.hom).π.app (op k) ≫ Ek.hom.left =
        (EG.symm ≪≫ EP).hom.left ≫ (modelScalarCone S P.hom).π.app (op k)) ∧
      IsPullback qPk cFN.pt.hom (stageScalarModel S P.hom k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qPk ≫ pullback.snd κ P.hom = qP ∧
      ∀ i, ∃ qBk : (cBN i).pt.left ⟶ (stageScalarModel S (cBM i).pt.hom k).left,
        IsClosedImmersion (chosenScalarArrow κ (jM i) ≫ Ek.hom).left ∧
        IsPullback qBk (cBN i).pt.hom (stageScalarModel S (cBM i).pt.hom k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
        qBk ≫ (chosenScalarArrow κ (jM i) ≫ Ek.hom).left = (jN i).left ≫ qPk ∧
        qBk ≫ pullback.snd κ (cBM i).pt.hom = qB i ∧
        LocallyOfFinitePresentation (stageScalarModel S (cBM i).pt.hom k).hom ∧
        CompactSpace (stageScalarModel S (cBM i).pt.hom k).left ∧
        QuasiSeparatedSpace (stageScalarModel S (cBM i).pt.hom k).left

/-- The specified closed coordinate atlases construct closed targets in one
scalar extension of the specified ambient model. Their original inclusions,
coordinate quotient legs, ambient comparison and both scalar projections are retained. -/
theorem exists_prefix_targets
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] [Finite C]
    {I : Type v} (F₀ : C ⥤ CommAlgCat.{u} S) (B₀ : I → C ⥤ CommAlgCat.{u} S)
    (F : C ⥤ CommAlgCat.{u} K) (B : I → C ⥤ CommAlgCat.{u} K)
    (eF : ∀ c, K ⊗[S] F₀.obj c ≃ₐ[K] F.obj c)
    (eB : ∀ i c, K ⊗[S] (B₀ i).obj c ≃ₐ[K] (B i).obj c)
    [∀ c, Algebra.FinitePresentation S (F₀.obj c)]
    [∀ i c, Algebra.FinitePresentation S ((B₀ i).obj c)]
    (hF : ∀ c d (f : c ⟶ d), (eF d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map f).hom) =
      (F.map f).hom.comp (eF c).toAlgHom)
    (hB : ∀ i c d (f : c ⟶ d), (eB i d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map f).hom) =
      ((B i).map f).hom.comp (eB i c).toAlgHom)
    (β₀ : ∀ i, F₀ ⟶ B₀ i) (β : ∀ i, F ⟶ B i)
    (hβ : ∀ i c, (eB i c).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((β₀ i).app c).hom) =
      ((β i).app c).hom.comp (eF c).toAlgHom)
    [∀ {c d} (f : c ⟶ d), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F₀.map f).hom.toRingHom))]
    [((F₀.op ⋙ algSpec (.of S) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (hcart : ∀ i,
      (Functor.whiskerRight (NatTrans.op (β₀ i))
        (algSpec (.of S) ⋙ Over.forget _)).Equifibered)
    (hclosed : ∀ i c, IsClosedImmersion
      (Spec.map (CommRingCat.ofHom ((β₀ i).app c).hom.toRingHom)))
    (cFN : Cocone (F.op ⋙ algSpec (.of K))) (hcFN : IsColimit cFN)
    (cBN : ∀ i, Cocone ((B i).op ⋙ algSpec (.of K)))
    (hcBN : ∀ i, IsColimit (cBN i)) (jN : ∀ i, (cBN i).pt ⟶ cFN.pt)
    (hjN : ∀ i c, (cBN i).ι.app c ≫ jN i =
      (algSpec (.of K)).map ((β i).app c.unop).op ≫ cFN.ι.app c)
    (P : Over (Spec (.of S))) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    [LocallyOfFinitePresentation P.hom] (qP : cFN.pt.left ⟶ P.left)
    (hP : IsPullback qP cFN.pt.hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S) :
    target_result S F₀ B₀ β₀ F B eF eB hF hB cFN cBN jN P qP hP start := by
  let : IsNoetherianRing S := isNoetherianRing_of_fg hS
  obtain ⟨cFM, qF, hcFM, hqF, hlegsF, hcompactF, hfpF⟩ :=
    exists_affine_model_for_colimit F₀ F eF hF cFN hcFN
  have hmodels (i : I) := exists_closed_model_in_atlas F₀ (B₀ i) F (B i) eF (eB i)
    hF (hB i) (β₀ i) (β i) (hcart i) (hclosed i) cFN (cBN i) (hcBN i)
    cFM hcFM.some qF hlegsF (jN i) (hjN i)
    (fun c => quotient_comparison (eF c.unop) (eB i c.unop)
      ((β₀ i).app c.unop) ((β i).app c.unop) (hβ i c.unop)
      ((affineModelNatTrans F₀ F eF hF).app c)
      ((affineModelNatTrans (B₀ i) (B i) (eB i) (hB i)).app c) rfl rfl)
  choose cBM qB jM hcBM hjM hqB hlegsB hlegsM hcompare hcompactB hfpB using hmodels
  let : CompactSpace cFM.pt.left := hcompactF
  let : LocallyOfFinitePresentation cFM.pt.hom := hfpF
  let : IsLocallyNoetherian cFM.pt.left := LocallyOfFiniteType.isLocallyNoetherian cFM.pt.hom
  let : QuasiSeparatedSpace cFM.pt.left := inferInstance
  let (i : I) : CompactSpace (cBM i).pt.left := hcompactB i
  let (i : I) : LocallyOfFinitePresentation (cBM i).pt.hom := hfpB i
  let (i : I) : IsClosedImmersion (jM i).left := hjM i
  let EG : cFN.pt ≅ genericScalarModel S cFM.pt.hom := hqF.flip.isoOverPullback
  let EP : cFN.pt ≅ genericScalarModel S P.hom := hP.flip.isoOverPullback
  let E := EG.symm ≪≫ EP
  obtain ⟨i, Ei, hEi, _⟩ := exists_model_iso S hS cFM.pt.hom P.hom E
  obtain ⟨k, hstart, hik⟩ := exists_ge_ge start i
  let Ek := retainedIsoExtend S cFM.pt.hom P.hom hik Ei
  have hEk : (modelScalarCone S cFM.pt.hom).π.app (op k) ≫ Ek.hom.left =
      E.hom.left ≫ (modelScalarCone S P.hom).π.app (op k) :=
    extendModelMorphism_baseChange S cFM.pt.hom P.hom hik Ei.hom E.hom hEi
  refine ⟨cFM, cBM, qF, qB, jM, hcFM, hcBM, hjM, hqF, hqB, hlegsF, hlegsB,
    hlegsM, hcompare,
    k, hstart, Ek, hEk, overIso_modelStage_cartesian S P.hom k cFN.pt EP,
    ?_, fun r => ?_⟩
  · exact original_triangle EP.hom.left _ _ _ qP (cone_original S P k)
      hP.flip.isoOverPullback_hom_left_comp_snd
  · let EB : (cBN r).pt ≅ genericScalarModel S (cBM r).pt.hom :=
      (hqB r).flip.isoOverPullback
    exact ⟨EB.hom.left ≫ (modelScalarCone S (cBM r).pt.hom).π.app (op k),
      target_stage S hS (qB r) qF (hqB r) hqF (jM r) (jN r)
        (hcompare r) k EG EP rfl E rfl Ek hEk⟩

end SchubertGeometry
