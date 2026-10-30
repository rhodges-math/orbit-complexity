import OrbitComplexity.SchubertGeometry.Connectedness.PairedAuxiliaryModels
import OrbitComplexity.SchubertGeometry.Connectedness.PairedSourceModels
import OrbitComplexity.SchubertGeometry.Connectedness.PairedModelIntegral
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Integral fibres of the prescribed paired model

Both word endpoints and closed Schubert targets are constructed before
applying the connectedness criterion. The source and endpoint in the
conclusion are successive scalar extensions of the prescribed models.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

open private WordFlagModels.stage WordFlagModels.afterStart
  WordFlagModels.source WordFlagModels.target WordFlagModels.flag
  WordFlagModels.endpoint WordFlagModels.inclusion
  WordFlagModels.sourceProper WordFlagModels.sourceSmooth WordFlagModels.endpointProper
  WordFlagModels.targetFp WordFlagModels.inclusionClosed
  WordFlagModels.flagFp WordFlagModels.flagQc WordFlagModels.flagSeparated
  WordFlagModels.qSource WordFlagModels.qTarget WordFlagModels.qFlag
  WordFlagModels.sourceCartesian WordFlagModels.targetCartesian WordFlagModels.flagCartesian
  WordFlagModels.endpointSquare WordFlagModels.inclusionSquare
  WordFlagModels.flagProjection WordFlagModels.projectionCartesian
  WordFlagModels.originalProjection
  from OrbitComplexity.SchubertGeometry.Connectedness.WordFlagModels
open private paired_source_models
  from OrbitComplexity.SchubertGeometry.Connectedness.PairedSourceModels
open private scalar_fp
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

/-- The prescribed smooth paired source acquires integral normal-domain
field fibres after successive coefficient enlargements. Its prescribed
endpoint becomes proper and geometrically connected, and its prescribed
Richardson target becomes geometrically connected over the coefficient ring. -/
theorem exists_chosen_integral_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a))
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [Smooth C.hom]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation D.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (e : C ⟶ D) (r : D ⟶ F) [IsClosedImmersion r.left]
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD)
    (hr : qD ≫ r.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).left ≫ qF)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k) (l : CoefficientStage k.val),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
      let CT := stageScalarModel S C.hom k
      let DT := stageScalarModel S D.hom k
      GeometricallyConnected (chosenScalarArrow τ (chosenScalarArrow κ e)).left ∧
      IsProper (chosenScalarArrow τ (chosenScalarArrow κ e)).left ∧
      GeometricallyConnected (stageScalarModel k.val DT.hom l).hom ∧
      ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of l.val)),
        IsIntegral (pullback s (stageScalarModel k.val CT.hom l).hom : Scheme.{u}) ∧
        ∀ x : (pullback s (stageScalarModel k.val CT.hom l).hom : Scheme.{u}),
          IsDomain ((pullback s (stageScalarModel k.val CT.hom l).hom :
            Scheme.{u}).presheaf.stalk x) ∧
          IsIntegrallyClosed ((pullback s (stageScalarModel k.val CT.hom l).hom :
            Scheme.{u}).presheaf.stalk x) := by
  obtain ⟨data⟩ := exists_paired_auxiliary_models G a b ha hb S hS F qF hF start
  let k := WordFlagModels.stage data
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let : QuasiCompact κ := quasiCompact_of_compactSpace κ
  let : QuasiSeparated κ := QuasiSeparated.of_quasiSeparatedSpace κ
  let CT := stageScalarModel S C.hom k
  let DT := stageScalarModel S D.hom k
  let eT : CT ⟶ DT := chosenScalarArrow κ e
  let X := WordFlagModels.source data ⟨false⟩
  let Y := WordFlagModels.source data ⟨true⟩
  let U := WordFlagModels.target data ⟨false⟩
  let V := WordFlagModels.target data ⟨true⟩
  let P := WordFlagModels.flag data
  let f : X ⟶ U := WordFlagModels.endpoint data ⟨false⟩
  let g : Y ⟶ V := WordFlagModels.endpoint data ⟨true⟩
  let i : U ⟶ P := WordFlagModels.inclusion data ⟨false⟩
  let j : V ⟶ P := WordFlagModels.inclusion data ⟨true⟩
  obtain ⟨rT, qCT, qDT, hrTclosed, hCT, hDT, _hCTo, _hDTo, heT, hrT⟩ :=
    paired_source_models S C D F e r (pairedBSDHSource G a b)
      (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver
      (pairedRichardsonMap G a b ha hb)
      (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)) qC qD qF hC hD hF he hr k P
      (WordFlagModels.flagProjection data) (WordFlagModels.projectionCartesian data)
      (WordFlagModels.qFlag data) (WordFlagModels.flagCartesian data)
      (WordFlagModels.originalProjection data)
  let : QuasiCompact (pullback.snd κ C.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback κ C.hom) (inferInstance : QuasiCompact κ)
  let : QuasiSeparated (pullback.snd κ C.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback κ C.hom) (inferInstance : QuasiSeparated κ)
  let : CompactSpace CT.left := by
    change CompactSpace (pullback κ C.hom : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd κ C.hom)
  let : QuasiSeparatedSpace CT.left := by
    change QuasiSeparatedSpace (pullback κ C.hom : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd κ C.hom)
  let : Smooth CT.hom := by
    change Smooth (pullback.fst κ C.hom)
    infer_instance
  let : QuasiCompact (pullback.snd κ D.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback κ D.hom) (inferInstance : QuasiCompact κ)
  let : QuasiSeparated (pullback.snd κ D.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback κ D.hom) (inferInstance : QuasiSeparated κ)
  let : CompactSpace DT.left := by
    change CompactSpace (pullback κ D.hom : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd κ D.hom)
  let : QuasiSeparatedSpace DT.left := by
    change QuasiSeparatedSpace (pullback κ D.hom : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd κ D.hom)
  let : LocallyOfFinitePresentation DT.hom := scalar_fp κ D
  let : IsProper X.hom := WordFlagModels.sourceProper data ⟨false⟩
  let : IsProper Y.hom := WordFlagModels.sourceProper data ⟨true⟩
  let : Smooth X.hom := WordFlagModels.sourceSmooth data ⟨false⟩
  let : Smooth Y.hom := WordFlagModels.sourceSmooth data ⟨true⟩
  let : LocallyOfFinitePresentation U.hom := WordFlagModels.targetFp data ⟨false⟩
  let : LocallyOfFinitePresentation V.hom := WordFlagModels.targetFp data ⟨true⟩
  let : LocallyOfFinitePresentation P.hom := WordFlagModels.flagFp data
  let : QuasiCompact P.hom := WordFlagModels.flagQc data
  let : IsSeparated P.hom := WordFlagModels.flagSeparated data
  let : IsProper f.left := WordFlagModels.endpointProper data ⟨false⟩
  let : IsProper g.left := WordFlagModels.endpointProper data ⟨true⟩
  let : IsClosedImmersion i.left := WordFlagModels.inclusionClosed data ⟨false⟩
  let : IsClosedImmersion j.left := WordFlagModels.inclusionClosed data ⟨true⟩
  let : IsClosedImmersion rT.left := hrTclosed
  obtain ⟨l, _hl, hgc, hp, hDgc, hfields, _hretained⟩ :=
    exists_paired_integral_model G a b ha hb hab k.val k.property.1 CT DT X Y U V P
      eT rT f g i j
      (WordFlagModels.qSource data ⟨false⟩) (WordFlagModels.qSource data ⟨true⟩)
      (WordFlagModels.qTarget data ⟨false⟩) (WordFlagModels.qTarget data ⟨true⟩)
      (WordFlagModels.qFlag data) qCT qDT
      (WordFlagModels.sourceCartesian data ⟨false⟩)
      (WordFlagModels.sourceCartesian data ⟨true⟩)
      (WordFlagModels.targetCartesian data ⟨false⟩)
      (WordFlagModels.targetCartesian data ⟨true⟩)
      (WordFlagModels.flagCartesian data) hCT hDT
      (WordFlagModels.endpointSquare data ⟨false⟩)
      (WordFlagModels.endpointSquare data ⟨true⟩)
      (WordFlagModels.inclusionSquare data ⟨false⟩)
      (WordFlagModels.inclusionSquare data ⟨true⟩) heT hrT
      ⟨k.val, k.property.1, le_rfl⟩
  exact ⟨k, WordFlagModels.afterStart data, l, hgc, hp, hDgc, hfields⟩

end SchubertGeometry
