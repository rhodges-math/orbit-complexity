import OrbitComplexity.SchubertGeometry.Connectedness.ChosenSchubertPair
import OrbitComplexity.SchubertGeometry.Connectedness.WordFlagModels
import OrbitComplexity.SchubertGeometry.Connectedness.PairedEndpointConnected
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Both word endpoints over a prescribed flag model

The ordinary and opposite targets and their proper smooth word sources
are constructed on one coefficient stage. Their comparisons retain the
flag projection, both endpoint maps and both closed inclusions.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private WordFlagModels
  WordFlagModels.mk
  WordFlagModels.stage
  WordFlagModels.afterStart
  WordFlagModels.source
  WordFlagModels.target
  WordFlagModels.flag
  WordFlagModels.endpoint
  WordFlagModels.inclusion
  WordFlagModels.sourceProper
  WordFlagModels.sourceSmooth
  WordFlagModels.endpointProper
  WordFlagModels.targetFp
  WordFlagModels.inclusionClosed
  WordFlagModels.flagFp
  WordFlagModels.flagQc
  WordFlagModels.flagSeparated
  WordFlagModels.qSource
  WordFlagModels.qTarget
  WordFlagModels.qFlag
  WordFlagModels.sourceCartesian
  WordFlagModels.targetCartesian
  WordFlagModels.flagCartesian
  WordFlagModels.endpointSquare
  WordFlagModels.inclusionSquare
  WordFlagModels.flagProjection
  WordFlagModels.projectionCartesian
  WordFlagModels.originalProjection
  from OrbitComplexity.SchubertGeometry.Connectedness.WordFlagModels
open private inclusion_spec_comp
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
open private scalar_fp scalar_qc
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

private def earlier_flag_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {I : Type v}
    (G : ReductiveGroupData K) (words : I → List G.rootBase.support)
    (Y : I → Over (Spec (.of K))) (FK : Over (Spec (.of K)))
    (fK : ∀ i, Over.mk (bsdhToSpec G (words i)) ⟶ Y i) (jK : ∀ i, Y i ⟶ FK)
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    (P : Over (Spec (.of S))) (P₁ : Over (Spec (.of R)))
    (π : P₁.left ⟶ P.left)
    (hπ : IsPullback π P₁.hom P.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom)))
    (qP : FK.left ⟶ P.left) (qP₁ : FK.left ⟶ P₁.left) (hOld : qP₁ ≫ π = qP)
    (start : CoefficientStage S) (start₁ : CoefficientStage R)
    (hstart : start.val ≤ R)
    (data : WordFlagModels G words Y FK fK jK R P₁ qP₁ start₁) :
    WordFlagModels G words Y FK fK jK S P qP start := by
  let T : CoefficientStage S :=
    ⟨(WordFlagModels.stage data).val, (WordFlagModels.stage data).property.1, hSR.trans
      (WordFlagModels.stage data).property.2⟩
  have hπ' : IsPullback ((WordFlagModels.flagProjection data) ≫ π) (WordFlagModels.flag data).hom
    P.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion T.property.2).toRingHom)) := by
    have h := (WordFlagModels.projectionCartesian data).paste_horiz hπ
    simpa only [inclusion_spec_comp] using h
  have hOld' : (WordFlagModels.qFlag data) ≫ ((WordFlagModels.flagProjection data) ≫ π) = qP := by
    rw [← Category.assoc, (WordFlagModels.originalProjection data), hOld]
  exact WordFlagModels.mk
    (T)
    (hstart.trans (WordFlagModels.stage data).property.2)
    (WordFlagModels.source data)
    (WordFlagModels.target data)
    (WordFlagModels.flag data)
    (WordFlagModels.endpoint data)
    (WordFlagModels.inclusion data)
    (WordFlagModels.sourceProper data)
    (WordFlagModels.sourceSmooth data)
    (WordFlagModels.endpointProper data)
    (WordFlagModels.targetFp data)
    (WordFlagModels.inclusionClosed data)
    (WordFlagModels.flagFp data)
    (WordFlagModels.flagQc data)
    (WordFlagModels.flagSeparated data)
    (WordFlagModels.qSource data)
    (WordFlagModels.qTarget data)
    (WordFlagModels.qFlag data)
    (WordFlagModels.sourceCartesian data)
    (WordFlagModels.targetCartesian data)
    (WordFlagModels.flagCartesian data)
    (WordFlagModels.endpointSquare data)
    (WordFlagModels.inclusionSquare data)
    ((WordFlagModels.flagProjection data) ≫ π)
    (hπ')
    (hOld')

private abbrev pair_words {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support) :
    ULift.{u} Bool → List G.rootBase.support :=
  fun x => match x.down with | false => a | true => b

private abbrev pair_targets {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (v w : G.weylGroup) :
    ULift.{u} Bool → Over (Spec (.of K)) :=
  fun x => match x.down with
    | false => (schubertVariety G w).toOver
    | true => (oppositeSchubertVariety G v).toOver

private def pair_inclusions {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (v w : G.weylGroup) :
    ∀ x, pair_targets G v w x ⟶ (flagVariety G).toOver := by
  rintro ⟨x⟩
  cases x
  · exact schubertInclusion G w
  · exact oppositeSchubertInclusion G v

private def pair_endpoints {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b) :
    ∀ x, Over.mk (bsdhToSpec G (pair_words G a b x)) ⟶
      pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a) x := by
  rintro ⟨x⟩
  cases x
  · exact bsdhSchubertMap G a ha
  · exact bsdhOppositeSchubertMap G b hb

/-- The two word sources, their ordinary and opposite targets, and the
flag model exist together over a scalar extension of the prescribed
coefficient ring. All comparisons and closed inclusion squares persist. -/
theorem exists_paired_auxiliary_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    Nonempty (WordFlagModels G (pair_words G a b)
      (pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)) (flagVariety G).toOver
      (pair_endpoints G a b ha hb)
      (pair_inclusions G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)) S P qF start) := by
  let : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  obtain ⟨k, hk, U, V, i, j, qPk, qU, qV, hPk, hOld,
    hincU, hU, htriU, hfpU, _hcompactU, _hqsU,
    hincV, hV, htriV, hfpV, _hcompactV, _hqsV⟩ :=
    exists_chosen_schubert_pair G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a) S hS P qF hF start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let Pk := stageScalarModel S P.hom k
  let : LocallyOfFinitePresentation Pk.hom := scalar_fp κ P
  let : QuasiCompact Pk.hom := scalar_qc κ P
  let : IsSeparated Pk.hom := by
    change IsSeparated (pullback.fst κ P.hom)
    infer_instance
  let : IsClosedImmersion i.left := hincU
  let : IsClosedImmersion j.left := hincV
  let : IsSeparated U.hom := by
    rw [← i.w]
    infer_instance
  let : IsSeparated V.hom := by
    rw [← j.w]
    infer_instance
  let D : ULift.{u} Bool → Over (Spec (.of k.val)) :=
    fun x => match x.down with | false => U | true => V
  let inc : ∀ x, D x ⟶ Pk := by
    rintro ⟨x⟩
    cases x
    · exact i
    · exact j
  let qD : ∀ x,
      (pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a) x).left ⟶ (D x).left := by
    rintro ⟨x⟩
    cases x
    · exact qU
    · exact qV
  let (x : ULift.{u} Bool) : LocallyOfFinitePresentation (D x).hom := by
    rcases x with ⟨x⟩
    cases x
    · exact hfpU
    · exact hfpV
  let (x : ULift.{u} Bool) : IsSeparated (D x).hom := by
    rcases x with ⟨x⟩
    cases x <;> infer_instance
  let (x : ULift.{u} Bool) : IsClosedImmersion (inc x).left := by
    rcases x with ⟨x⟩
    cases x <;> infer_instance
  have hD : ∀ x, IsPullback (qD x)
      (pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a) x).hom (D x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) := by
    rintro ⟨x⟩
    cases x
    · exact hU
    · exact hV
  have hinc : ∀ x, qD x ≫ (inc x).left =
      (pair_inclusions G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a) x).left ≫ qPk := by
    rintro ⟨x⟩
    cases x
    · exact htriU
    · exact htriV
  obtain ⟨data⟩ := exists_word_flag_models G (pair_words G a b)
    (pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) (flagVariety G).toOver
    (pair_endpoints G a b ha hb)
    (pair_inclusions G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) k.val k.property.1 D Pk inc qD qPk hD hPk hinc
      ⟨k.val, k.property.1, le_rfl⟩
  exact ⟨earlier_flag_models G (pair_words G a b)
    (pair_targets G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) (flagVariety G).toOver
    (pair_endpoints G a b ha hb)
    (pair_inclusions G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) S k.val k.property.2 P Pk
    (pullback.snd κ P.hom) (IsPullback.of_hasPullback κ P.hom).flip
    qF qPk hOld start ⟨k.val, k.property.1, le_rfl⟩ hk data⟩

end SchubertGeometry
