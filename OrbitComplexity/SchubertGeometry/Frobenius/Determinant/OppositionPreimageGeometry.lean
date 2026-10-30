import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageChartCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOpenStages
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarPolynomialSquare
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Preimages of flag charts

The pullback of an open flag chart under a proper word map is smooth over the
coefficient ring and compact when the chart is affine.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting GroupActions ReductiveGroups
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.DeterminantSection.scalarMorphism
  SchubertGeometry.DeterminantSection.scalarMorphism_projection
  SchubertGeometry.DeterminantSection.cartesian_map
  SchubertGeometry.DeterminantSection.compactBaseChange from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOpenStages
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private preimageFst preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

/-- The preimage of a flag chart under the word map, over the coefficient base. -/
def chartPreimageModel {R : Type u} [CommRing R]
    (C W F : Over (Spec (.of R))) (i : C ⟶ F) (f : W ⟶ F) :
    Over (Spec (.of R)) :=
  Over.mk (pullback.snd i.left f.left ≫ W.hom)

/-- The projection from the chart preimage to its word model. -/
def chartPreimageWord {R : Type u} [CommRing R]
    (C W F : Over (Spec (.of R))) (i : C ⟶ F) (f : W ⟶ F) :
    (chartPreimageModel C W F i f).left ⟶ W.left :=
  pullback.snd i.left f.left

/-- The projection from the chart preimage to its flag chart. -/
def chartPreimageChart {R : Type u} [CommRing R]
    (C W F : Over (Spec (.of R))) (i : C ⟶ F) (f : W ⟶ F) :
    (chartPreimageModel C W F i f).left ⟶ C.left :=
  pullback.fst i.left f.left

/-- The projection to the chart as a morphism over the coefficient base. -/
def chartPreimageArrow {R : Type u} [rComm : CommRing R]
    {C W F : Over (Spec (.of R))} (i : C ⟶ F) (f : W ⟶ F) :
    @chartPreimageModel R rComm C W F i f ⟶ C :=
  Over.homMk (@chartPreimageChart R rComm C W F i f) (by
    change pullback.fst i.left f.left ≫ C.hom =
      pullback.snd i.left f.left ≫ W.hom
    calc
      _ = (pullback.fst i.left f.left ≫ i.left) ≫ F.hom := by
        rw [Category.assoc, i.w]
      _ = (pullback.snd i.left f.left ≫ f.left) ≫ F.hom :=
        congrArg (· ≫ F.hom) pullback.condition
      _ = _ := by rw [Category.assoc, f.w])

/-- A closed subscheme in an open chart is compact, quasi-separated and
locally of finite presentation when the chart and target have these properties. -/
theorem chartPreimage_closed_properties {R : Type u} [rComm : CommRing R]
    {C W F : Over (Spec (.of R))} (i : C ⟶ F) (f : W ⟶ F)
    (hOpen : IsOpenImmersion i.left) (hClosed : IsClosedImmersion f.left)
    (hCompact : CompactSpace C.left) (hQS : QuasiSeparatedSpace C.left)
    (hFP : LocallyOfFinitePresentation W.hom) :
    CompactSpace (@chartPreimageModel R rComm C W F i f).left ∧
      QuasiSeparatedSpace (@chartPreimageModel R rComm C W F i f).left ∧
      LocallyOfFinitePresentation (@chartPreimageModel R rComm C W F i f).hom := by
  let : IsOpenImmersion i.left := hOpen
  let : IsClosedImmersion f.left := hClosed
  let : CompactSpace C.left := hCompact
  let : QuasiSeparatedSpace C.left := hQS
  let : LocallyOfFinitePresentation W.hom := hFP
  refine ⟨?_, ?_, ?_⟩
  · change CompactSpace (pullback i.left f.left : Scheme.{u})
    exact (Scheme.Hom.isClosedEmbedding (pullback.fst i.left f.left)).compactSpace
  · change QuasiSeparatedSpace (pullback i.left f.left : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst i.left f.left)
  · change LocallyOfFinitePresentation (pullback.snd i.left f.left ≫ W.hom)
    infer_instance

private theorem preimage_properties {B : Scheme.{u}} (C W F : Over B)
    (i : C ⟶ F) (f : W ⟶ F)
    [IsOpenImmersion i.left] [IsProper f.left] [Smooth W.hom]
    [IsSeparated W.hom] [CompactSpace C.left] :
    IsOpenImmersion (pullback.snd i.left f.left) ∧
      IsProper (pullback.fst i.left f.left) ∧
    Smooth (pullback.snd i.left f.left ≫ W.hom) ∧
      IsSeparated (pullback.snd i.left f.left ≫ W.hom) ∧
        CompactSpace (pullback i.left f.left : Scheme.{u}) := by
  have h : IsPullback (pullback.fst i.left f.left)
      (pullback.snd i.left f.left) i.left f.left :=
    IsPullback.of_hasPullback i.left f.left
  let : IsOpenImmersion (pullback.snd i.left f.left) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h inferInstance
  let : IsProper (pullback.fst i.left f.left) :=
    MorphismProperty.of_isPullback (P := @IsProper) h.flip inferInstance
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst i.left f.left)

/-- An open flag chart pulled back along a proper word map is a smooth,
separated, compact scheme over the same coefficient ring. -/
theorem chartPreimageModel_properties {R : Type u} [CommRing R]
    (C W F : Over (Spec (.of R))) (i : C ⟶ F) (f : W ⟶ F)
    [IsOpenImmersion i.left] [IsProper f.left] [Smooth W.hom]
    [IsSeparated W.hom] [CompactSpace C.left] :
    IsOpenImmersion (chartPreimageWord C W F i f) ∧
      IsProper (chartPreimageChart C W F i f) ∧
    Smooth (chartPreimageModel C W F i f).hom ∧
      IsSeparated (chartPreimageModel C W F i f).hom ∧
        CompactSpace (chartPreimageModel C W F i f).left :=
  preimage_properties C W F i f

private theorem compare_preimages {B T : Scheme.{u}} (κ : T ⟶ B)
    (C W F : Over B) (CK WK FK : Over T)
    (i : C ⟶ F) (f : W ⟶ F) (iK : CK ⟶ FK) (fK : WK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qW : WK.left ⟶ W.left) (qF : FK.left ⟶ F.left)
    (hC : IsPullback qC CK.hom C.hom κ)
    (hW : IsPullback qW WK.hom W.hom κ)
    (hF : IsPullback qF FK.hom F.hom κ)
    (hi : iK.left ≫ qF = qC ≫ i.left)
    (hf : fK.left ≫ qF = qW ≫ f.left)
    {P : Scheme.{u}} (pC : P ⟶ CK.left) (pW : P ⟶ WK.left)
    (hP : IsPullback pC pW iK.left fK.left) :
    ∃ n : P ⟶ pullback i.left f.left,
      n ≫ pullback.fst i.left f.left = pC ≫ qC ∧
      n ≫ pullback.snd i.left f.left = pW ≫ qW ∧
      IsPullback n (pW ≫ WK.hom) (pullback.snd i.left f.left ≫ W.hom) κ := by
  have hiK : IsPullback iK.left qC qF i.left :=
    SchubertGeometry.DeterminantSection.cartesian_map κ C F CK FK i qC qF hC hF iK hi
  have houter : IsPullback (pC ≫ qC) pW i.left (qW ≫ f.left) := by
    have h := hP.paste_horiz hiK.flip
    rw [hf] at h
    exact h
  let n : P ⟶ pullback i.left f.left :=
    pullback.lift (pC ≫ qC) (pW ≫ qW)
      (houter.w.trans (Category.assoc _ _ _).symm)
  have hnC : n ≫ pullback.fst i.left f.left = pC ≫ qC := pullback.lift_fst _ _ _
  have hnW : n ≫ pullback.snd i.left f.left = pW ≫ qW := pullback.lift_snd _ _ _
  have houter' : IsPullback (n ≫ pullback.fst i.left f.left) pW i.left
      (qW ≫ f.left) := by
    rw [hnC]
    exact houter
  have hn : IsPullback n pW (pullback.snd i.left f.left) qW :=
    IsPullback.of_right houter' hnW (IsPullback.of_hasPullback i.left f.left)
  exact ⟨n, hnC, hnW, hn.paste_vert hW⟩

/-- The preimage on the scalar fibre maps canonically to the preimage model,
with the same chart and word projections and a Cartesian coefficient square. -/
theorem exists_chartPreimage_scalar {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (C W F : Over (Spec (.of R)))
    (CK WK FK : Over (Spec (.of K)))
    (i : C ⟶ F) (f : W ⟶ F) (iK : CK ⟶ FK) (fK : WK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qW : WK.left ⟶ W.left) (qF : FK.left ⟶ F.left)
    (hC : IsPullback qC CK.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hW : IsPullback qW WK.hom W.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hF : IsPullback qF FK.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hi : iK.left ≫ qF = qC ≫ i.left)
    (hf : fK.left ≫ qF = qW ≫ f.left)
    {P : Scheme.{u}} (pC : P ⟶ CK.left) (pW : P ⟶ WK.left)
    (hP : IsPullback pC pW iK.left fK.left) :
    ∃ n : P ⟶ (chartPreimageModel C W F i f).left,
      n ≫ chartPreimageChart C W F i f = pC ≫ qC ∧
      n ≫ chartPreimageWord C W F i f = pW ≫ qW ∧
      IsPullback n (pW ≫ WK.hom) (chartPreimageModel C W F i f).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  compare_preimages (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    C W F CK WK FK i f iK fK qC qW qF hC hW hF hi hf pC pW hP

private theorem pullback_id_comp {X Y Z : Scheme.{u}} (i : X ⟶ Z) (f : Y ⟶ Z) :
    IsPullback (pullback.fst i (𝟙 Y ≫ f)) (pullback.snd i (𝟙 Y ≫ f)) i f := by
  simpa only [Category.id_comp] using (IsPullback.of_hasPullback i (𝟙 Y ≫ f))

/-- The opposition chart pulls back to a smooth compact model of the same
word-chart preimage, retaining its word and polynomial coordinate projections. -/
theorem exists_opposition_preimage_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : PrefixModel G word) (r : G.rootBase.support)
    (S : Subalgebra ℤ K) (hMS : M.S ≤ S)
    {C : Over (Spec (.of S))} [cCompact : CompactSpace C.left]
    (qChart : (affineVariety K
      (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G r))).toOver.left ⟶ C.left)
    (hC : IsPullback qChart
      (affineVariety K
        (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G r))).toOver.hom
      C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W F : Over (Spec (.of S)))
    (qOriginal : W.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal W.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom)))
    (qW : bsdhScheme G word ⟶ W.left)
    (hW : IsPullback qW (bsdhToSpec G word) W.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hOriginalWord : qW ≫ qOriginal = M.m₀)
    (qF : (flagVariety G).toOver.left ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toOver.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (i : C ⟶ F) [iOpen : IsOpenImmersion i.left]
    (f : W ⟶ F) [fProper : IsProper f.left]
    (hi : (@DeterminantSection.oppositionPolynomialMap.{u}
      K kField kClosed kZero G r).left ≫ qF =
        qChart ≫ i.left)
    (hf : bsdhMap G word ≫ qF = qW ≫ f.left) :
    let Y0 := chartPreimageModel C W F i f
    CompactSpace Y0.left ∧ Smooth Y0.hom ∧ Y0.left.IsSeparated ∧
      ∃ z : wordChartPreimage G word (𝟙 (bsdhScheme G word)) r ⟶ Y0.left,
        IsPullback z
          (preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ M.fieldCocone.pt.hom)
          Y0.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
        z ≫ chartPreimageWord C W F i f =
          preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ qW ∧
        z ≫ (chartPreimageWord C W F i f ≫ qOriginal) =
          preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ M.m₀ ∧
        IsPullback (chartPreimageChart C W F i f) (chartPreimageWord C W F i f)
          i.left f.left ∧
        z ≫ chartPreimageChart C W F i f =
          preimageFst G word (𝟙 (bsdhScheme G word)) r ≫
            qChart := by
  intro Y0
  let : Smooth W.hom := MorphismProperty.of_isPullback (P := @Smooth) hOriginal M.smoothModel
  let : IsProper W.hom := MorphismProperty.of_isPullback (P := @IsProper) hOriginal M.proper
  have properties := @chartPreimageModel_properties.{u} S (inferInstanceAs (CommRing S))
    C W F i f iOpen fProper inferInstance inferInstance cCompact
  obtain ⟨_, _, hsmooth, hsep, hcompact⟩ := properties
  let : IsSeparated Y0.hom := hsep
  have hYsep : Y0.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from Y0.hom]
    infer_instance
  let WK : Over (Spec (.of K)) := Over.mk (bsdhToSpec G word)
  let fK : WK ⟶ (flagVariety G).toOver :=
    Over.homMk (bsdhMap G word) rfl
  have hcomparison := @exists_chartPreimage_scalar.{u}
    S K (inferInstanceAs (CommRing S)) kField.toCommRing
    (inferInstanceAs (Algebra S K)) C W F
    (affineVariety K (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G r))).toOver WK
      (flagVariety G).toOver
    i f (@DeterminantSection.oppositionPolynomialMap.{u} K kField kClosed kZero G r) fK
    qChart qW qF hC hW hF hi hf
    (wordChartPreimage G word (𝟙 (bsdhScheme G word)) r)
    (preimageFst G word (𝟙 (bsdhScheme G word)) r)
    (preimageSnd G word (𝟙 (bsdhScheme G word)) r)
    (pullback_id_comp
      (@DeterminantSection.oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
      (bsdhMap G word))
  obtain ⟨z, hzC, hzW, hz⟩ := hcomparison
  refine ⟨hcompact, hsmooth, hYsep, z, hz, hzW, ?_,
    IsPullback.of_hasPullback _ _, hzC⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ qOriginal) hzW).trans
      ((Category.assoc _ _ _).trans
        (congrArg (preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ ·) hOriginalWord)))

end SchubertGeometry.RetainedCharacter
