import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionStage
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordAppendSplitting
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial coefficients on successive word models

The word coefficient data is carried through the same scalar models.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000
set_option maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

open RetainedCharacter

universe u v

open private initialCoefficient finalCoefficient polynomialSpecMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private borelPolynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendBorelCharts
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private coordinateScalarBase coordinateScalarMap fieldCoordinateCocone
  fieldCoordinateCocone_colimit fieldCoordinateDiagram_opens fieldCoordinateMap
  inverseCoordinates_affine retainedCoordinateRings singleCoordinateRings
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private map_exists_witness map_and_tail from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel

open private appendChartTriangle firstCoefficient firstChartIsos firstChartSquare firstChartBase
  scalarChartIsos scalarChartSquare scalarChartBase AppendChartData AppendChartContext
      AppendChartStage
  contextChartIsos contextRetentionData retain_chart_context fieldSchemeIso fieldSchemeIso_base
      fieldSchemeIso_left from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

open private AppendChartData.mk AppendChartData.I AppendChartData.F
  AppendChartData.N AppendChartData.e AppendChartData.sel
  AppendChartData.V₀ AppendChartData.p AppendChartData.c
  AppendChartData.g AppendChartData.a₀ AppendChartData.hend
  AppendChartData.b AppendChartData.hbbase AppendChartContext.mk
  AppendChartContext.D AppendChartContext.eP AppendChartContext.cD
  AppendChartContext.hOpen AppendChartContext.hCover AppendChartContext.base
  AppendChartContext.m AppendChartContext.hCart
  AppendChartContext.hfield AppendChartContext.hprior
  AppendChartStage.mk AppendChartStage.q AppendChartStage.hm
  AppendChartStage.V AppendChartStage.finite AppendChartStage.affine
  AppendChartStage.index AppendChartStage.eV AppendChartStage.hold
  AppendChartStage.hbase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private selectedFrame selectedIndex from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private wordPolynomialData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private coefficientTailResult coefficientScalarValues stageRetentionResult
  appendAlgST appendAlgTR appendAlgSR appendTowerSTK appendTowerTRK appendTowerSRK
  appendTowerSTR from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionStage

section WordStage

variable {K : Type u} [hField : Field K] [hClosed : IsAlgClosed K] [hZero : CharZero K]
    (G : ReductiveGroupData K) (prior : List (@simpleRootIndex.{u} K hField hClosed hZero G))
    (i : (@simpleRootIndex.{u} K hField hClosed hZero G)) (S T R : Subalgebra ℤ K) (hST : S ≤ T)
        (hTR : T ≤ R)

variable [hSTFact : Fact (S ≤ T)] [hTRFact : Fact (T ≤ R)] [hSRFact : Fact (S ≤ R)]

attribute [local instance] appendAlgST appendAlgTR appendAlgSR appendTowerSTK
  appendTowerTRK appendTowerSRK appendTowerSTR

variable {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (qK : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G)))) ⟶ Y)
    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    {input : @AppendChartData.{u} K hField hClosed hZero S₀ G prior i} (old :
        @AppendChartContext.{u} K hField hClosed hZero S₀ G prior i input)
    (d : @AppendChartStage.{u} K hField hClosed hZero S₀ G prior i S hS₀ input old Y base qK)
    {J : Type u} (U : J → Y.Opens)


variable
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
          hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)
          prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).map
          f).hom.toRingHom))]
    [hFdir : ((((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).op
          ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).op
          ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (hptF : cF.pt = Over.mk (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed
        hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G))))))
    (q : cF.pt.left ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)
        prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G)))))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
        hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)
        prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (@List.append.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G))))))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, @chartLift.{u} K hField hClosed hZero G J
        ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a s j hj =
      @chartLift.{u} K hField hClosed hZero G J ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, @wordTransitionUnit.{u} K hField hClosed hZero G J
        ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj l hl =
      @wordTransitionUnit.{u} K hField hClosed hZero G J ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s k hk l hl * @wordTransitionUnit.{u} K hField hClosed hZero G J
          ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).map
          f).hom.toMonoidHom (@wordTransitionUnit.{u} K hField hClosed hZero G J
          ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk) =
        @wordTransitionUnit.{u} K hField hClosed hZero G J ((@intersectionCoordinates.{u,u,u} K
            (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
            hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed
            hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (e : ∀ s, K ⊗[S] ((@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K hField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S) Y base
      {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
          (intersectionOpens U))).obj s ≃ₐ[K] ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s)
    (he : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s) k *
        @fieldCoordinateMap.{u} S K (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
            K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K
            hField))) S) (@Field.toCommRing K hField) Y (bsdhScheme G (@List.append.{u}
            (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
            (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
            hField hClosed hZero G))))) base (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K
            hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed
            hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK J U s
            x)
    (v : (@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) R) (@appendAlgST.{u} K hField S T hSTFact)
        (@appendAlgTR.{u} K hField T R hTRFact) Y base J U) ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) ⋙
          forget₂ (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, (v.app s).hom x =
      (@coefficientScalarValues.{u} K hField S T R hSTFact hTRFact Y base J U
      ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) e)
          s x)
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing
          K (@Field.toDivisionRing K hField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K hField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K hField))) R) (@appendAlgST.{u} K hField S T hSTFact)
          (@appendAlgTR.{u} K hField T R hTRFact) Y base J U).obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : (@retainedCoordinateRings.{u} S T R
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) T)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) R)
        (@appendAlgST.{u} K hField S T hSTFact) (@appendAlgTR.{u} K hField T R hTRFact) Y base J
        U).obj s) =
      (@wordTransitionUnit.{u} K hField hClosed hZero G J ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk : ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s))
    (hcoN : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K hField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K hField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K hField))) R) (@appendAlgST.{u} K hField S T hSTFact)
          (@appendAlgTR.{u} K hField T R hTRFact) Y base J U).map f).hom.toMonoidHom (delta s j hj k
          hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial ((@retainedCoordinateRings.{u} S T R
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) T)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) R)
        (@appendAlgST.{u} K hField S T hSTFact) (@appendAlgTR.{u} K hField T R hTRFact) Y base J
        U).obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      @wordRingCoefficient.{u} K hField hClosed hZero G J ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K hField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a j)

private def coefficientRetentionResult : Prop :=
  @coefficientTailResult.{u} K hField hClosed hZero G J
    ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a beta i R (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) R)
    (@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) R) (@appendAlgST.{u} K hField S T hSTFact)
        (@appendAlgTR.{u} K hField T R hTRFact) Y base J U)
    (@coefficientScalarValues.{u} K hField S T R hSTFact hTRFact Y base J U
      ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) e)
    T.FG R.FG
    (fun v hv delta hd hcoN hnN P hP =>
      @stageRetentionResult.{u} K hField hClosed hZero G prior i S T R hST hTR
        hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d J U
        @hFopen hFdir cF hcF hptF q point a ha beta hgroup hco hn
        v hv delta hd hcoN hnN P hP)


omit [IsProper base] in
private theorem retain_coefficient_result
    (hq : (@fieldSchemeIso.{u} (Spec (.of K)) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u}
        K hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
        G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G))))) cF.pt (bsdhToSpec G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G))))) hptF).hom = q)
    (hdS : IsPullback (AppendChartStage.q d) base (AppendChartContext.base old)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (h :
      let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
      @matchingRetainedResult.{u} K hField hClosed hZero G S Y (bsdhScheme G (@List.append.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G))))) base (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK J U @hFopen
          hFdir cF hcF hptF
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
            (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
            hField hClosed hZero G)))) q point a ha beta hgroup hco hn i e
        (AppendChartStage.V d) (fun j => (@firstCoefficient.{u} S₀ S (@Subalgebra.toCommRing ℤ K
            Int.instCommRing (@Field.toCommRing K hField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S₀) (@Subalgebra.toCommRing ℤ
            K Int.instCommRing (@Field.toCommRing K hField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S) (Subalgebra.inclusion
            hS₀).toAlgebra ((AppendChartData.N input).obj ((AppendChartStage.index d) j).1)))
        (fun j => @CommAlgCat.instCommRingObjForgetAlgHomCarrier S (@Subalgebra.toCommRing ℤ K
            Int.instCommRing (@Field.toCommRing K hField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S) (@firstCoefficient.{u} S₀
            S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S₀)
            (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S)
            (Subalgebra.inclusion hS₀).toAlgebra ((AppendChartData.N input).obj
            ((AppendChartStage.index d) j).1)))
        (fun j => @CommAlgCat.instAlgebraObjForgetAlgHomCarrier S (@Subalgebra.toCommRing ℤ K
            Int.instCommRing (@Field.toCommRing K hField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S) (@firstCoefficient.{u} S₀
            S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S₀)
            (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) S)
            (Subalgebra.inclusion hS₀).toAlgebra ((AppendChartData.N input).obj
            ((AppendChartStage.index d) j).1))) (AppendChartStage.eV d) T hST R hTR) :
    @coefficientRetentionResult.{u} K hField hClosed hZero G prior i S T R hST hTR
      hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d J U
      @hFopen hFdir cF hcF hptF q point a ha beta hgroup hco hn e := by
  let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
  show @coefficientTailResult.{u} K hField hClosed hZero G J
    ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a beta i R (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K hField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K hField))) R)
    (@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K hField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K hField))) R) (@appendAlgST.{u} K hField S T hSTFact)
        (@appendAlgTR.{u} K hField T R hTRFact) Y base J U)
    (@coefficientScalarValues.{u} K hField S T R hSTFact hTRFact Y base J U
      ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K hField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          hField hClosed hZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K hField hClosed hZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K hField hClosed hZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) e)
    T.FG R.FG
    (fun v hv delta hd hcoN hnN P hP =>
      @stageRetentionResult.{u} K hField hClosed hZero G prior i S T R hST hTR
        hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d J U
        @hFopen hFdir cF hcF hptF q point a ha beta hgroup hco hn
        v hv delta hd hcoN hnN P hP)
  refine map_and_tail h ?_
  intro hT h
  refine map_and_tail h ?_
  intro hR h
  refine map_exists_witness h ?_
  intro v h
  refine map_exists_witness h ?_
  intro hev h
  refine map_exists_witness h ?_
  intro hv h
  refine map_exists_witness h ?_
  intro delta h
  refine map_exists_witness h ?_
  intro hd h
  refine map_exists_witness h ?_
  intro hcoN h
  refine map_exists_witness h ?_
  intro hnN h
  refine map_exists_witness h ?_
  intro P h
  refine map_exists_witness h ?_
  intro hpoly h
  refine map_exists_witness h ?_
  intro hP h
  refine map_and_tail h ?_
  intro hr hstage
  exact @retained_word_sections.{u} K hField hClosed hZero G prior i S T R hST hTR
    hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d J U @hFopen hFdir cF hcF hptF q point a ha
        beta
    hgroup hco hn v hv delta hd hcoN hnN P hP hq hR hdS hstage

end WordStage


end SchubertGeometry
