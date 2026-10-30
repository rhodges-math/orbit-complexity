import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionApplication
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained geometry of an appended word

The same coefficient models, polynomial cover and character-line comparisons
supply the arithmetic model and omitted-letter boundaries of the new word.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
open private scalar_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private append_scalar_record from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionApplication

open private retain_append_models append_earlier_boundary_fields
  append_last_boundary_fields from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionApplication
open private coordinate_comparison fixedFibreDiagram_smooth_twice projection_evaluation from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private AppendChartData AppendChartData.N AppendChartContext AppendChartContext.mk
  AppendChartStage AppendChartStage.q AppendChartStage.hm from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
open private retainedCoordinateRings fieldCoordinateCocone fieldCoordinateCocone_colimit
  fieldCoordinateDiagram_opens inverseCoordinates_affine coordinateScalarBase
  coordinateScalarMap fieldCoordinateMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private selectedIndex selectedIndex_mem from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private inverseOpenDiagram from
  OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private intersectionCoordinates_smooth from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels
open private appendAlgST appendAlgTR appendAlgSR appendTowerSTK appendTowerTRK
  appendTowerSRK appendTowerSTR from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionStage

namespace SchubertGeometry

open RetainedCharacter

section Geometry

attribute [local instance] appendAlgST appendAlgTR appendAlgSR appendTowerSTK
  appendTowerTRK appendTowerSRK appendTowerSTR

/-- The retained append charts determine one new-word geometry with its line and boundaries. -/
theorem exists_append_geometry {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word)
    (i : @simpleRootIndex.{u} K kField kClosed kZero G)
    (L : @NextLetter.{u} K kField kClosed kZero G word M i) :
    Nonempty (@AppendGeometry.{u} K kField kClosed kZero G word M i L) := by
  obtain ⟨coefficients, prior, hRoot, hCoefficients, hAtlas⟩ :=
    @retain_append_models.{u} K kField kClosed kZero G word M i L
  obtain ⟨c₀, a₀, hc₀, ha₀, hco, hn, D, eP, π, hπmap, hD, hπ,
    cD, q, ⟨hcD⟩, hqlegs, hqcart, hproper, hsmooth, hconnected,
    hOpen, hCover, m, hmCart, hmAppend, hProjective, hPolynomial,
    S, hRS, δ₀, hδClosed, hδSection, hδNode, dNative, hdπ, hdτ, hdNative,
    hStage⟩ := hAtlas
  obtain ⟨hS, Y, base, qS, mS, hproperS, hsmoothS, hScart, hKcart,
    hmS, W, hfiniteW, haffW, V, hfiniteV, haffV, index, eV,
    hVcart, hVbase, hVold, hWord⟩ := hStage
  obtain ⟨point, a, ha, beta, hgroup, hnatural, hbeta, e, he, henat,
    T, hST, R, hTR, hCoeff⟩ := hWord
  obtain ⟨hT, hR, v, hev, hv, delta, hdelta, hcoN, hnN,
    P, hP, hCoefficient, hr, hStageResult⟩ := hCoeff
  obtain ⟨hJ, hVfinite, hsm, cArithmetic, hpt, hcN, hCart,
    hprojection, hNopen, hNdir, ESections, hESections, hSections,
    hModels⟩ := hStageResult
  obtain ⟨hWfinite, hWaff, hqNcart, hproperN, hsmoothN, hsepN, dR, hdR, hCommonSmooth,
    hCommonField, Q, hRQ, hQ, πField, jK, hV, hword, hπField, hjKb, hCommon⟩ := hModels
  let hSTFact : Fact (S ≤ T) := ⟨hST⟩
  let hTRFact : Fact (T ≤ R) := ⟨hTR⟩
  let hSRFact : Fact (S ≤ R) := ⟨hST.trans hTR⟩
  let : Fact (S ≤ T) := hSTFact
  let : Fact (T ≤ R) := hTRFact
  let : Fact (S ≤ R) := hSRFact
  let : IsProper base := hproperS
  let : Smooth base := hsm
  let := @wordSchemeSeparated.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K
      kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
      (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
  let U : W.I₀ → Y.Opens := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := haffW j
    exact isAffineOpen_opensRange (W.f j)
  let M₀ : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} S :=
    (@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset W.I₀ // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset W.I₀ //
          s.Nonempty})) (intersectionOpens U))
  let F : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} K :=
    (@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset W.I₀ // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (@inverseOpenDiagram.{u,u,u} Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) mS {s : Finset
          W.I₀ // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (intersectionOpens U)))
  let hEK := inverseCoordinates_affine (S := S) (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
        mS hKcart U hU
  let cF : Cocone (F.op ⋙ algSpec (.of K)) := fieldCoordinateCocone (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
        mS U hEK
  let hcF : IsColimit cF := fieldCoordinateCocone_colimit (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
        mS U
    W.iSup_opensRange hEK
  let N := @retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
    (@appendAlgTR.{u} K kField T R hTRFact) Y base W.I₀ U
  let cN := retainedCoordinateCocone (S := S) (T := T) (R := R) M₀ cArithmetic
  let qN := scalarModelProjection N F v cN cF hcF
  have hCart' : IsPullback qN (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
      kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G))))) cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := hCart
  obtain ⟨eR, hCanonical, heR, hERV⟩ :=
    @coordinate_comparison.{u} K kField S T R hST hTR
      {s : Finset W.I₀ // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
      M₀ F e henat N rfl v (fun s x => (hev s x).symm)
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from base]
    infer_instance⟩
  have hSmooth0 : ∀ s, Algebra.Smooth S (M₀.obj s) := by
    intro s
    let : Smooth (((intersectionOpens U).obj (op s)).ι ≫ base) := inferInstance
    exact
      @intersectionCoordinates_smooth.{u} Y W.I₀ S (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) S)
        (inferInstanceAs (IsAffineHom (pullback.diagonal (terminal.from Y))))
        base U hU s
        (inferInstanceAs (Smooth (((intersectionOpens U).obj (op s)).ι ≫ base)))
  have hSmoothNodes : ∀ s, Algebra.Smooth R (N.obj s) :=
    @fixedFibreDiagram_smooth_twice.{u,u,u}
      {s : Finset W.I₀ // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
      S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      (@appendAlgST.{u} K kField S T hSTFact)
      (@appendAlgTR.{u} K kField T R hTRFact) M₀ hSmooth0
  have hFiniteNodes : ∀ s, Algebra.FinitePresentation R (N.obj s) := by
    intro s
    let := hSmoothNodes s
    infer_instance
  let stageMap := AppendChartStage.q dR
  have hmStage : qN ≫ stageMap = m := AppendChartStage.hm dR
  obtain ⟨B, hclosedB, ⟨nB, hnB⟩, hBeforeEq, hLastEq, hBefore, hLast⟩ :=
    @exists_word_boundary_models.{u} K kField kClosed kZero G word i
      prior.cT.pt.left cD.pt q m prior.mT hmAppend
      δ₀ hδSection hδClosed dNative hdπ hdτ hdNative
      prior.boundaries prior.hclosed prior.nB prior.hnB
      cN.pt.left stageMap qN hmStage
  have hbmodel := @projection_evaluation.{u,u,u} R K
    (inferInstanceAs (CommRing R)) (@Field.toCommRing K kField)
    (inferInstanceAs (Algebra R K)) {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
    N F v eR hERV cN cF hcF qN rfl
  have hMR : M.S ≤ R :=
    coefficients.hMT.trans (prior.hMT.trans (hRS.trans (hST.trans hTR)))
  have hTwo : IsUnit (2 : R) := by
    simpa only [map_ofNat] using M.twoUnit.map (Subalgebra.inclusion hMR).toRingHom
  have hFieldDiagram := @fieldCoordinateDiagram_opens.{u}
    S K (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
        (@Field.toCommRing K kField) (inferInstanceAs (Algebra S K))
    Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (inferInstanceAs ((bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G))))).IsSeparated))
    base (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) mS hKcart W.I₀ U hU
  have hCoefficientConnected : GeometricallyConnected coefficients.cT.pt.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      coefficients.hqT M.connected
  have hPriorConnected : GeometricallyConnected prior.cT.pt.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      prior.hqT hCoefficientConnected
  let : GeometricallyConnected q := hconnected
  let : GeometricallyConnected prior.cT.pt.hom := hPriorConnected
  let : Smooth q := hsmooth
  let : Smooth prior.cT.pt.hom := prior.smoothModel
  have hAppendConnected : GeometricallyConnected (q ≫ prior.cT.pt.hom) :=
    GeometricallyConnected.comp q prior.cT.pt.hom
  have hBaseConnected : GeometricallyConnected base :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      hScart hAppendConnected
  have hModelConnected : GeometricallyConnected cN.pt.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      hqNcart hBaseConnected
  let pre : @PrefixModel.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K
      kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
      (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) :=
    @PrefixModel.mk.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField
        kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
      R hR hTwo W.I₀ hJ F N eR heR
      (fun {s t} f => hFieldDiagram.1 s t f) hFieldDiagram.2
      hNopen hNdir hFiniteNodes hSmoothNodes
      (fun s => ⟨@selectedIndex.{u} W.I₀ s, @selectedIndex_mem.{u} W.I₀ s⟩)
      cF.ι hcF cN hcN qN hCart' hbmodel hproperN hsmoothN hModelConnected
      point a ha beta hgroup hnatural hbeta
      v hv hERV delta hdelta hcoN hnN
      P (fun s => (hP s).1) hr hCoefficient B hclosedB nB hnB
  let input := @NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
    coefficients prior
  let old : @AppendChartContext.{u} K kField kClosed kZero prior.T G word i input :=
    @AppendChartContext.mk.{u} K kField kClosed kZero prior.T G word i input
      D eP cD hOpen hCover (q ≫ prior.cT.pt.hom) m hmCart
      (fun s j => (hPolynomial s j).1)
      (fun s j => (hPolynomial s j).2.2)
  let geometry : @AppendGeometryBase.{u} K kField kClosed kZero G word M i L :=
    @AppendGeometryBase.mk.{u} K kField kClosed kZero G word M i L
      coefficients prior old π hπ hπmap hcD q hmAppend rfl (fun s => hqlegs (op s))
      (fun {s t} f => c₀ t (M.sel t).val (M.sel t).property
        (M.sel s).val ((leOfHom f) (M.sel s).property))
      (fun {s t} f => a₀ t (M.sel t).val (M.sel t).property
        (M.sel s).val ((leOfHom f) (M.sel s).property))
      (fun {s t} f => hD s t f) pre (hRS.trans (hST.trans hTR))
  obtain ⟨earlierMap, hEarlier⟩ :=
    @append_earlier_boundary_fields.{u} K kField kClosed kZero G word M i L
      geometry dR hBefore
  obtain ⟨lastMap, hLast'⟩ :=
    @append_last_boundary_fields.{u} K kField kClosed kZero G word M i L
      geometry dR δ₀ hLast
  exact ⟨@AppendGeometry.mk.{u} K kField kClosed kZero G word M i L
    geometry dR hdR hRoot δ₀ hδClosed hδSection hδNode
    earlierMap hEarlier lastMap hLast' ESections hESections
    πField jK hV hword hπField hjKb Q hRQ hQ hCommon⟩


end Geometry

end SchubertGeometry
