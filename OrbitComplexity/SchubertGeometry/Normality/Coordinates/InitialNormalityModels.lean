import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenNormalityModels
import OrbitComplexity.SchubertGeometry.Normality.CompatibleIdealCover
import OrbitComplexity.SchubertGeometry.Connectedness.InitialRichardsonDiagram
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.SeparatedStages
import Batteries.Tactic.Lint

/-! # Arithmetic models for Richardson normality

The reduced-word diagram and separated flag stage provide the models on
which the proper endpoint and integral normal source fibres are retained.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting ReductiveGroups
namespace SchubertGeometry
universe u

open private comparison_at_stage from
  OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource
open private exists_arrow_scalar from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages
open private stage_properties from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private stageProjection factor_cartesian pullback_base_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages
open private spec_triangle from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected



private theorem separated_comparison {B T X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ T) (κ : T ⟶ B) (q : Y ⟶ X)
    (h : IsPullback q g f κ) [IsSeparated g] :
    IsSeparated (pullback.fst κ f) := by
  let E : Over.mk g ≅ Over.mk (pullback.fst κ f) := h.flip.isoOverPullback
  have hE : E.inv.left ≫ g = pullback.fst κ f := E.inv.w
  rw [← hE]
  infer_instance

private theorem noetherian_scalar {B T X : Scheme.{u}}
    (κ : T ⟶ B) (f : X ⟶ B) [IsNoetherian T] [CompactSpace X]
    [QuasiSeparatedSpace B] [LocallyOfFiniteType f] :
    IsNoetherian (pullback κ f : Scheme.{u}) := by
  let : QuasiCompact f := quasiCompact_of_compactSpace f
  let : CompactSpace (pullback κ f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst κ f)
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

private theorem scalar_closed {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (chosenScalarArrow κ f).left :=
  MorphismProperty.of_isPullback (chosenScalarArrow_cartesian κ f).flip inferInstance

/-- An arithmetic Richardson diagram has a smooth paired source, a closed target
in a separated flag model, Cartesian generic-fibre comparisons, and proper
geometrically connected endpoints with integral normal source fibres on later
coefficient stages. -/
def initialNormalityData {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b) : Prop :=
  ∃ (S : Subalgebra ℤ K) (C D F : Over (Spec (.of S)))
    (e : C ⟶ D) (j : D ⟶ F)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left),
    S.FG ∧ IsNoetherian C.left ∧ IsNoetherian D.left ∧ IsNoetherian F.left ∧
    Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
    LocallyOfFinitePresentation D.hom ∧ LocallyOfFinitePresentation F.hom ∧
    IsSeparated F.hom ∧ IsClosedImmersion j.left ∧
    IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    IsPullback qD (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD ∧
    qD ≫ j.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ≫ qF ∧
    @normalityStages.{u} K (inferInstanceAs (Field K))
      (inferInstanceAs (IsAlgClosed K)) (inferInstanceAs (CharZero K))
      G a b ha hb S C D F e j qC qD qF

/-- Reduced words with nonempty Richardson interval admit a separated arithmetic
flag model, a smooth paired source and a closed Richardson target. Above every
coefficient stage, the same models retain proper connected endpoints, integral
source field fibres and their Cartesian comparisons. -/
theorem exists_initial_normality_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)) :
    initialNormalityData G a b ha hb := by
  have hdiagram := exists_initial_richardson_diagram G a b ha hb
  obtain ⟨S, C, D, F, e, j, qC, qD, qF, hS, hnC, hnD, hnF,
    hsmC, hfpC, hfpD, hfpF, hjclosed, hC, hD, hF, he, hj⟩ := hdiagram
  let : IsNoetherian C.left := hnC
  let : IsNoetherian D.left := hnD
  let : IsNoetherian F.left := hnF
  let : Smooth C.hom := hsmC
  let : LocallyOfFinitePresentation C.hom := hfpC
  let : LocallyOfFinitePresentation D.hom := hfpD
  let : LocallyOfFinitePresentation F.hom := hfpF
  let : IsClosedImmersion j.left := hjclosed
  let v := G.longestElement * simpleWeylWord G.rootBase b
  let w := simpleWeylWord G.rootBase a
  let eK := pairedRichardsonMap G a b ha hb
  let jK := richardsonInclusion G v w
  let σ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let : IsSeparated (genericScalarModel S F.hom).hom :=
    separated_comparison F.hom (flagVariety G).toSpec σ qF hF
  let start : CoefficientStage S := ⟨S, hS, le_rfl⟩
  obtain ⟨k, _hk, hsep⟩ := exists_separated_scalar_stage S hS F start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  have hρ : ρ ≫ κ = σ := by rw [← Spec.map_comp]; rfl
  let Ck := stageScalarModel S C.hom k
  let Dk := stageScalarModel S D.hom k
  let Fk := stageScalarModel S F.hom k
  let ek : Ck ⟶ Dk := chosenScalarArrow κ e
  let jk : Dk ⟶ Fk := chosenScalarArrow κ j
  let : IsNoetherianRing k.val := isNoetherianRing_of_fg k.property.1
  let : IsNoetherian Ck.left := noetherian_scalar κ C.hom
  let : IsNoetherian Dk.left := noetherian_scalar κ D.hom
  let : IsNoetherian Fk.left := noetherian_scalar κ F.hom
  let : Smooth Ck.hom := inferInstanceAs (Smooth (pullback.fst κ C.hom))
  let : LocallyOfFinitePresentation Ck.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ C.hom))
  let : LocallyOfFinitePresentation Dk.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ D.hom))
  let : LocallyOfFinitePresentation Fk.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst κ F.hom))
  let : IsSeparated Fk.hom := hsep
  let : IsClosedImmersion jk.left := scalar_closed κ j
  have hEbase := map_to_variety_base (pairedBSDHSource G a b)
    (richardsonVariety G v w) eK
  have hJbase := varietyMap_base (richardsonVariety G v w) (flagVariety G) jK
  have hcomparisons := diagram_stage_comparisons κ ρ σ hρ C D F
    (pairedBSDHSource G a b).hom (richardsonVariety G v w).toSpec (flagVariety G).toSpec
    eK.left jK.left hEbase hJbase e j qC qD qF hC hD hF he hj
  obtain ⟨mC, mD, mF, hCk, hDk, hFk, _hpC, _hpD, _hpF, hek, hjk⟩ := hcomparisons
  refine ⟨k.val, Ck, Dk, Fk, ek, jk, mC, mD, mF, k.property.1,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hsep, inferInstance, hCk, hDk, hFk, hek, hjk, ?_⟩
  exact @exists_chosen_normality_models.{u} K
    (inferInstanceAs (Field K)) (inferInstanceAs (IsAlgClosed K))
    (inferInstanceAs (CharZero K)) G a b ha hb hab k.val k.property.1
    Ck Dk Fk (inferInstanceAs (CompactSpace Ck.left))
    (inferInstanceAs (QuasiSeparatedSpace Ck.left)) (inferInstanceAs (Smooth Ck.hom))
    (inferInstanceAs (CompactSpace Dk.left)) (inferInstanceAs (QuasiSeparatedSpace Dk.left))
    (inferInstanceAs (LocallyOfFinitePresentation Dk.hom))
    (inferInstanceAs (LocallyOfFinitePresentation Fk.hom))
    (inferInstanceAs (QuasiCompact Fk.hom)) (inferInstanceAs (IsSeparated Fk.hom))
    ek jk (inferInstanceAs (IsClosedImmersion jk.left)) mC mD mF hCk hDk hFk hek hjk

/-- The same initial Richardson diagram admits a splitting on every positive
prime-characteristic fibre above a common coefficient bound, while retaining
its proper connected endpoint and integral normal source-fibre certificates. -/
theorem exists_richardson_split_models
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hle : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)) :
  ∃ (S : Subalgebra ℤ K) (C D F : Over (Spec (.of S)))
    (e : C ⟶ D) (j : D ⟶ F)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left),
    S.FG ∧ IsNoetherian C.left ∧ IsNoetherian D.left ∧ IsNoetherian F.left ∧
    Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
    LocallyOfFinitePresentation D.hom ∧ LocallyOfFinitePresentation F.hom ∧
    IsSeparated F.hom ∧ IsClosedImmersion j.left ∧
    IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    IsPullback qD (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD ∧
    qD ≫ j.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ≫ qF ∧
    @normalityStages.{u} K kField kClosed kZero G a b ha hb S C D F e j qC qD qF ∧
    ∀ start : CoefficientStage S, ∃ (bound : CoefficientStage S) (_ : start ≤ bound),
      ∀ (t : CoefficientStage S) (_ : bound ≤ t)
        (L : Type u) [_lField : Field L] (point : Spec (.of L) ⟶ Spec (.of t.val))
        (p : ℕ) [Fact p.Prime] [CharP L p],
        Nonempty (SchemeSplitting
          (pullback point (@stageScalarModel.{u} K kField.toCommRing S D.left D.hom t).hom :
            Scheme.{u}) p) := by
  classical
  have hInitial := @exists_initial_normality_models.{u} K kField kClosed kZero G a b ha hb hle
  obtain ⟨S, C, D, F, e, j, qC, qD, qF, hS, hCNoeth, hDNoeth, hFNoeth,
    hCSmooth, hCFP, hDFP, hFFP, hFSeparated, hjClosed, hC, hD, hF, he, hj, hStages⟩ := hInitial
  refine ⟨S, C, D, F, e, j, qC, qD, qF, hS, hCNoeth, hDNoeth, hFNoeth,
    hCSmooth, hCFP, hDFP, hFFP, hFSeparated, hjClosed, hC, hD, hF, he, hj, hStages, ?_⟩
  obtain ⟨word, hred, hword⟩ :=
    (weylCoxeterSystem G.rootBase).exists_isReduced G.longestElement
  have hw : simpleWeylWord G.rootBase word = G.longestElement := by
    simpa only [weylCoxeterSystem_wordProd] using hword.symm
  obtain ⟨M, hM, _hWordFields⟩ :=
    @RetainedCharacter.word_splitting.{u} K kField kClosed kZero G word
  let : IsNoetherian F.left := hFNoeth
  let : LocallyOfFinitePresentation F.hom := hFFP
  let : IsSeparated F.hom := hFSeparated
  let common : CoefficientStage S :=
    ⟨S ⊔ M.S, hS.sup M.hS, le_sup_left⟩
  obtain ⟨J, jFinite, U, hU, hcover⟩ :=
    @exists_finite_affine_opens.{u} (flagVariety G).scheme
      (inferInstanceAs (CompactSpace (flagVariety G).scheme))
  have hTargets := @exists_chosen_closed_targets.{u} K J G.weylGroup
    kField kClosed kZero jFinite (weylGroup_finite G.rootBase)
    G (fun w => schubertSupport G w) U hU hcover S hS F
    (inferInstanceAs (CompactSpace F.left)) hFFP qF hF common
  obtain ⟨k, hcommon, Dord, jord, qFk, qDord, hFk, hqFk, hord⟩ := hTargets
  have hMk : M.S ≤ k.val := (show M.S ≤ common.val from le_sup_right).trans hcommon
  let initialM : CoefficientStage M.S := ⟨k.val, k.property.1, hMk⟩
  let CM := stageScalarModel M.S M.cG.pt.hom initialM
  let qOriginal : CM.left ⟶ M.cG.pt.left :=
    pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion initialM.property.2).toRingHom))
      M.cG.pt.hom
  have hOriginal : IsPullback qOriginal CM.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion initialM.property.2).toRingHom)) :=
    (IsPullback.of_hasPullback _ _).flip
  obtain ⟨mCM, hmCM, hmOriginal⟩ :=
    @comparison_at_stage.{u} K kField.toCommRing M.S M.cG.pt.left M.cG.pt.hom
      initialM (Over.mk (bsdhToSpec G word)) M.m₀ M.hm₀
  let Fk := stageScalarModel S F.hom k
  have hFkCompact : CompactSpace Fk.left := by
    change CompactSpace (pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom :
        Scheme.{u})
    infer_instance
  have hFkSeparated : IsSeparated Fk.hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (IsPullback.of_hasPullback
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom).flip
      hFSeparated
  have hFkFP : LocallyOfFinitePresentation Fk.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom).flip
      hFFP
  have hDordCompact : ∀ w, CompactSpace (Dord w).left := fun w => (hord w).2.2.2.2.1
  have hDordQS : ∀ w, QuasiSeparatedSpace (Dord w).left := fun w => (hord w).2.2.2.2.2
  have hDordFP : ∀ w, LocallyOfFinitePresentation (Dord w).hom := fun w => (hord w).2.2.2.1
  have hjord : ∀ w, IsClosedImmersion (jord w).left := fun w => (hord w).1
  have hDord : ∀ w, IsPullback (qDord w) (schubertVariety G w).toOver.hom
      (Dord w).hom (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    fun w => (hord w).2.1
  have hTriangle : ∀ w,
      (schubertInclusion G w).left ≫ qFk = qDord w ≫ (jord w).left :=
    fun w => (hord w).2.2.1.symm
  let start : CoefficientStage initialM.val := ⟨k.val, k.property.1, le_rfl⟩
  have hSplitting := @exists_flag_splitting_stage.{u} K kField kClosed kZero G word
    M hM initialM CM Fk qOriginal hOriginal mCM hmCM hmOriginal hred hw Dord
    hFkCompact hFkSeparated hFkFP hDordCompact hDordQS hDordFP
    jord hjord qDord hDord qFk hFk hTriangle start
  obtain ⟨t, hstart, MT, FT, DT, OT, jT, jOT, endpoint, qMT, m, q, pFT, qDT, qOT,
    hqMT, hm, hq, hpFT, hqProjection, hqDT, hqOT, hDT, hOT,
    hFTFP, hFTCompact, hFTQS, hFTSeparated, hmOriginal', hEndpoint, hjT, hjOT,
    hBoundaryClosed, n, hn, rFlag, hFlag⟩ := hSplitting
  let geometry : CoefficientStage S :=
    ⟨t.val, t.property.1, k.property.2.trans t.property.2⟩
  let pFTold : FT.left ⟶ F.left :=
    pFT ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom
  have hCoefficients :
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hFTold : IsPullback pFTold FT.hom F.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom)) := by
    dsimp only [pFTold]
    rw [← hCoefficients]
    exact hpFT.paste_horiz (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom).flip
  have hqFTold : q ≫ pFTold = qF :=
    (Category.assoc q pFT (pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        F.hom)).symm.trans
        ((congrArg (fun z => z ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom)
          hqProjection).trans hqFk)
  let DR := @stageScalarModel.{u} K kField.toCommRing S D.left D.hom geometry
  let pDR := @stageProjection.{u} K kField.toCommRing S D.left D.hom geometry
  have hDRModel : IsPullback pDR DR.hom D.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom)) :=
    (IsPullback.of_hasPullback _ _).flip
  have hDArrow := @exists_arrow_scalar.{u} K kField.toCommRing S D F
    (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver qD hD qF j
    (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) hj.symm geometry FT pFTold hFTold q hq hqFTold
  obtain ⟨jDR, qDR, hJDRCartesian, hDRNative, _hDRProjection, hJDRNative, _hJDRProjection⟩ :=
    hDArrow
  let hJDRClosed : IsClosedImmersion jDR.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hJDRCartesian.flip hjClosed
  let : IsNoetherian D.left := hDNoeth
  have hDRProperties := @stage_properties.{u} K kField.toCommRing S hS D
    (inferInstanceAs (CompactSpace D.left)) hDFP geometry
  have hDRFP : LocallyOfFinitePresentation DR.hom := hDRProperties.1
  have hDRCompact : CompactSpace DR.left := hDRProperties.2.1
  have hDRQS : QuasiSeparatedSpace DR.left := hDRProperties.2.2
  have hMTProper : IsProper MT.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hqMT M.proper
  have hTargetSplits := @exists_split_target_stage.{u} K kField kClosed kZero G word M
    (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)
    t.val t.property.1 MT DR FT hMTProper hDRCompact hDRQS hDRFP
    hFTCompact hFTFP hFTSeparated DT OT jT jOT
    (fun w => (hDT w).1) (fun w => (hOT w).1) endpoint qMT rFlag hFlag
    jDR hJDRClosed qDR qDT qOT q hDRNative hqDT hqOT hq hJDRNative hjT hjOT rFlag
  obtain ⟨splitStage, _hStartSplit, _hFlagSplit, hSplit⟩ := hTargetSplits
  let splitBase := @singleScalarStage.{u} K kField.toCommRing S geometry splitStage
  intro start
  obtain ⟨bound, hStartBound, hSplitBound⟩ := exists_ge_ge start splitBase
  refine ⟨bound, hStartBound, ?_⟩
  intro later hBoundLater L lField point p hpPrime lChar
  have hSplitLater : splitBase ≤ later := hSplitBound.trans hBoundLater
  let laterL : Algebra later.val L := (Spec.preimage point).hom.toAlgebra
  let splitL : Algebra splitStage.val L :=
    ((@algebraMap later.val L _ _ laterL).comp
      (Subalgebra.inclusion hSplitLater).toRingHom).toAlgebra
  let Dlater := @stageScalarModel.{u} K kField.toCommRing S D.left D.hom later
  let Dκ : Over (Spec (.of L)) := Over.mk (pullback.fst point Dlater.hom)
  let qDold := pullback.snd point Dlater.hom ≫
    @stageProjection.{u} K kField.toCommRing S D.left D.hom later
  let betaLater := Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion later.property.2).toRingHom)
  let betaGeometry := Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom)
  let coefficientR := Spec.map (CommRingCat.ofHom
    ((@algebraMap splitStage.val L _ _ splitL).comp
      (Subalgebra.inclusion splitStage.property.2).toRingHom))
  let coefficientS := Spec.map (CommRingCat.ofHom
    ((@algebraMap later.val L _ _ laterL).comp
      (Subalgebra.inclusion later.property.2).toRingHom))
  have hSpecLater : Spec.map (CommRingCat.ofHom
      (@algebraMap later.val L _ _ laterL)) = point := Spec.map_preimage point
  have hOldCoefficient : point ≫ betaLater = coefficientS :=
    (congrArg (fun f => f ≫ betaLater) hSpecLater.symm).trans
      (@spec_triangle.{u} S later.val L (inferInstanceAs (CommRing S))
        (inferInstanceAs (CommRing later.val)) lField.toCommRing
        (Subalgebra.inclusion later.property.2).toRingHom
        (@algebraMap later.val L _ _ laterL)
        ((@algebraMap later.val L _ _ laterL).comp
          (Subalgebra.inclusion later.property.2).toRingHom) rfl)
  have hDold : IsPullback qDold Dκ.hom D.hom coefficientS :=
    pullback_base_eq
      ((IsPullback.of_hasPullback point Dlater.hom).flip.paste_horiz
        (IsPullback.of_hasPullback betaLater D.hom).flip) hOldCoefficient
  have hGeometryCoefficient : coefficientR ≫ betaGeometry = coefficientS :=
    @spec_triangle.{u} S t.val L (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing t.val)) lField.toCommRing
      (Subalgebra.inclusion geometry.property.2).toRingHom
      ((@algebraMap splitStage.val L _ _ splitL).comp
        (Subalgebra.inclusion splitStage.property.2).toRingHom)
      ((@algebraMap later.val L _ _ laterL).comp
        (Subalgebra.inclusion later.property.2).toRingHom) (by ext z; rfl)
  have hFactor := @factor_cartesian.{u} (Spec (.of S)) (Spec (.of t.val)) (Spec (.of L))
    betaGeometry coefficientR coefficientS hGeometryCoefficient D DR Dκ pDR qDold hDRModel hDold
  obtain ⟨qDRκ, _hDκProjection, hDκR⟩ := hFactor
  exact @hSplit L lField splitL Dκ qDRκ hDκR p hpPrime lChar

end SchubertGeometry
