import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word covers and their scalar models

Affine word covers retain their coefficient polynomials and scalar model maps.
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

open private coefficientRetentionResult retain_coefficient_result from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordStage

open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter

private theorem coordinateDiagram_properties
    {S K : Type u} [sComm : CommRing S] [kComm : CommRing K] [sKAlg : Algebra S K]
    {Y X : Scheme.{u}} [X.IsSeparated]
    (base : Y ⟶ Spec (.of S))
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {J : Type u} (U : J → Y.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (hF : F = (@intersectionCoordinates.{u,u,u} K kComm X baseK {s : Finset J // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
      (@inverseOpenDiagram.{u,u,u} Y X qK {s : Finset J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) :
    (∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))) ∧
    ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := by
  subst F
  let h := fieldCoordinateDiagram_opens (S := S) (K := K) (Y := Y) (X := X)
    base baseK qK hK U hU
  exact ⟨fun {_ _} f => h.1 _ _ f, h.2⟩


section CoverPacket

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (w : List (@simpleRootIndex.{u} K kField kClosed kZero G))
    (S : Subalgebra ℤ K) {J : Type u}
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (cF : Cocone (F.op ⋙ algSpec (.of K)))
    (q : cF.pt.left ⟶ bsdhScheme G w)
    (v : ∀ s, M.obj s →+* F.obj s)
    (Tail : ∀ (point : J → G.points)
      (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
        (oppositeUnipotentVariety G).toOver)
      (_ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
        (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G w))
      (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
      (_hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
        chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
      (_hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
        beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
          (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
      (_hbeta : ∀ s j hj k hk l hl,
        beta s j hj l hl = beta s k hk l hl * beta s j hj k hk)
      (_e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
      (T : Subalgebra ℤ K) (_hST : S ≤ T)
      (R : Subalgebra ℤ K) (_hTR : T ≤ R), Prop)

private def coverCoefficientResult : Prop :=
  ∃ (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G w))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
    ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (F.obj s) k * v s x) ∧
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom) ∧
      ∃ (T : Subalgebra ℤ K) (hST : S ≤ T)
        (R : Subalgebra ℤ K) (hTR : T ≤ R),
        Tail point a ha beta hgroup hnatural hbeta e T hST R hTR

end CoverPacket

section WordCover

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]

set_option cleanup.letToHave false in
private def wordCoverRetention
    (G : ReductiveGroupData K) (prior : List (@simpleRootIndex.{u} K kField kClosed kZero G)) (i :
        (@simpleRootIndex.{u} K kField kClosed kZero G))
    (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    [(bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))).IsSeparated]
    (qK : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) (hW : ∀ j, IsAffine (W.X j))
    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    {input : AppendChartData S₀ G prior i} (old : AppendChartContext input)
    (d : AppendChartStage S hS₀ old base qK) : Prop :=
  let U : W.I₀ → Y.Opens := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let M : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} S :=
    (@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset W.I₀ // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset W.I₀ //
          s.Nonempty})) (intersectionOpens U))
  let F : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} K :=
    (@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset W.I₀ // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (@inverseOpenDiagram.{u,u,u} Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset
          W.I₀ // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (intersectionOpens U)))
  let hEK := inverseCoordinates_affine (S := S) (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK hK U hU
  let cF : Cocone (F.op ⋙ algSpec (.of K)) := fieldCoordinateCocone (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK U hEK
  let hcF : IsColimit cF := fieldCoordinateCocone_colimit (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK U
    W.iSup_opensRange hEK
  let q : cF.pt.left ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero
      G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))) := 𝟙 (bsdhScheme G (@List.append.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K
      kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
  let hF := coordinateDiagram_properties (S := S) (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK hK U hU F rfl
  let hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    hF.1
  let hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected := hF.2
  coverCoefficientResult G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))) S M F cF q
    (fieldCoordinateMap (S := S) (K := K) (Y := Y)
      (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G))))) qK U)
    (fun point a ha beta hgroup hnatural hbeta e T hST R hTR =>
      let laws := @section_character_laws.{u,u} K kField kClosed kZero G W.I₀ F beta hnatural hbeta
      let hSTFact : Fact (S ≤ T) := ⟨hST⟩
      let hTRFact : Fact (T ≤ R) := ⟨hTR⟩
      let hSRFact : Fact (S ≤ R) := ⟨hST.trans hTR⟩
      @coefficientRetentionResult.{u} K kField kClosed kZero G prior i S T R hST hTR
        hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d W.I₀ U
        @hFopen hFdir cF hcF rfl q point a ha beta hgroup laws.1 laws.2 e)

variable (G : ReductiveGroupData K) (prior : List (@simpleRootIndex.{u} K kField kClosed kZero G))
    (i : (@simpleRootIndex.{u} K kField kClosed kZero G))
    (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    [(bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))).IsSeparated]
    (qK : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) (hW : ∀ j, IsAffine (W.X j))
    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    {input : AppendChartData S₀ G prior i} (old : AppendChartContext input)
    (d : AppendChartStage S hS₀ old base qK)

private theorem retain_word_cover
    (hdS : IsPullback (AppendChartStage.q d) base (AppendChartContext.base old)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (h :
      let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
      matchingWordCover G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))) i S base qK hK W hW (AppendChartStage.V
          d)
        (fun j => (firstCoefficient (A₁ := S) ((AppendChartData.N input).obj
            ((AppendChartStage.index d) j).1))) (AppendChartStage.eV d)) :
    wordCoverRetention G prior i S base qK hK W hW hS₀ old d := by
  let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
  let hU : ∀ j, IsAffineOpen ((W.f j).opensRange) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let hEK := inverseCoordinates_affine (S := S) (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK hK
    (fun j => (W.f j).opensRange) hU
  let cF := fieldCoordinateCocone (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK
    (fun j => (W.f j).opensRange) hEK
  let hcF := fieldCoordinateCocone_colimit (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK
    (fun j => (W.f j).opensRange) W.iSup_opensRange hEK
  let F : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} K :=
    (@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset W.I₀ // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (@inverseOpenDiagram.{u,u,u} Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset
          W.I₀ // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty}))
          (intersectionOpens (fun j => (W.f j).opensRange))))
  let hF := coordinateDiagram_properties (S := S) (K := K) (Y := Y)
    (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G))))) qK hK
      (fun j => (W.f j).opensRange) hU F rfl
  let hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) := hF.1
  let hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected := hF.2
  apply map_exists_witness h
  intro point h
  apply map_exists_witness h
  intro a h
  apply map_exists_witness h
  intro ha h
  apply map_exists_witness h
  intro beta h
  apply map_exists_witness h
  intro hgroup h
  apply map_exists_witness h
  intro hnatural h
  apply map_exists_witness h
  intro hbeta h
  apply map_exists_witness h
  intro e h
  apply map_and_tail h
  intro he h
  apply map_and_tail h
  intro henat h
  apply map_exists_witness h
  intro T h
  apply map_exists_witness h
  intro hST h
  apply map_exists_witness h
  intro R h
  apply map_exists_witness h
  intro hTR h
  let hSTFact : Fact (S ≤ T) := ⟨hST⟩
  let hTRFact : Fact (T ≤ R) := ⟨hTR⟩
  let hSRFact : Fact (S ≤ R) := ⟨hST.trans hTR⟩
  exact @retain_coefficient_result.{u} K kField kClosed kZero G prior i S T R hST hTR
    hSTFact hTRFact hSRFact Y base qK S₀ hS₀ input old d W.I₀
    (fun j => (W.f j).opensRange) @hFopen hFdir cF hcF rfl (𝟙 _) point a ha beta hgroup
    (@section_character_laws.{u,u} K kField kClosed kZero G W.I₀ F beta hnatural hbeta).1
    (@section_character_laws.{u,u} K kField kClosed kZero G W.I₀ F beta hnatural hbeta).2 e rfl hdS
        h

end WordCover


open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels

section ScalarStage

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (prior : List (@simpleRootIndex.{u} K kField kClosed kZero G)) (i :
        (@simpleRootIndex.{u} K kField kClosed kZero G))
    (S : Subalgebra ℤ K) (input : AppendChartData S G prior i)
    (old : AppendChartContext input)

private def wordStageRetention (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  let := wordSchemeSeparated G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
      prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G))))
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
    (qT : YT ⟶ (AppendChartContext.cD old).pt) (mT : bsdhScheme G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G)))) ⟶ YT)
    (hproper : IsProper baseT) (hsmooth : Smooth baseT)
    (_hTcart : IsPullback qT baseT (AppendChartContext.base old)
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hKcart : IsPullback mT (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
        kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (hmT : mT ≫ qT = (AppendChartContext.m old)),
    ∃ (W : YT.OpenCover.{u}) (hfiniteW : Finite W.I₀) (haffW : ∀ j, IsAffine (W.X j)),
    let : Finite W.I₀ := hfiniteW
    let : IsProper baseT := hproper
    let : Smooth baseT := hsmooth
    ∃ (V : YT.OpenCover.{u}) (hfiniteV : Finite V.I₀)
      (haffV : ∀ j, IsAffine (V.X j))
      (index : V.I₀ ≃ (appendPolynomialCover (AppendChartData.N input) (AppendChartContext.D old)
          (AppendChartContext.eP old) (AppendChartContext.cD old)
        (AppendChartContext.hOpen old) (AppendChartContext.hCover old)).I₀)
      (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (T ⊗[S] (AppendChartData.N input).obj (index
          j).1)))),
      let : Finite V.I₀ := hfiniteV
      let : ∀ j, IsAffine (V.X j) := haffV
      (∀ j, IsPullback
        ((eV j).hom ≫ polynomialSpecMap (Algebra.TensorProduct.includeRight :
          (AppendChartData.N input).obj (index j).1 →ₐ[S] T ⊗[S] (AppendChartData.N input).obj
              (index j).1).toRingHom)
        (V.f j) ((appendPolynomialCover (AppendChartData.N input) (AppendChartContext.D old)
            (AppendChartContext.eP old) (AppendChartContext.cD old)
          (AppendChartContext.hOpen old) (AppendChartContext.hCover old)).f (index j)) qT) ∧
      ∃ (hVbase : ∀ j, V.f j ≫ baseT = (eV j).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap T
            (Polynomial (T ⊗[S] (AppendChartData.N input).obj (index j).1)))))
        (hVold : ∀ j, V.f j ≫ qT = (eV j).hom ≫
          polynomialSpecMap (Algebra.TensorProduct.includeRight :
            (AppendChartData.N input).obj (index j).1 →ₐ[S] T ⊗[S] (AppendChartData.N input).obj
                (index j).1).toRingHom ≫
              (appendPolynomialCover (AppendChartData.N input) (AppendChartContext.D old)
                  (AppendChartContext.eP old) (AppendChartContext.cD old)
                (AppendChartContext.hOpen old) (AppendChartContext.hCover old)).f (index j)),
        let d : AppendChartStage T hST old baseT mT :=
          @AppendChartStage.mk.{u} K kField kClosed kZero S G prior i T hST input old YT baseT mT
            qT hmT V hfiniteV haffV index eV hVold hVbase
        wordCoverRetention G prior i T baseT mT hKcart W haffW hST old d

private theorem retain_word_scalar_stage (T : Subalgebra ℤ K) (hST : S ≤ T)
    (h :
      let := wordSchemeSeparated G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
          prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))
      matchingWordStage G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))) i S (AppendChartContext.base old)
          (AppendChartContext.m old)
        (appendPolynomialCover (AppendChartData.N input) (AppendChartContext.D old)
            (AppendChartContext.eP old) (AppendChartContext.cD old) (AppendChartContext.hOpen old)
            (AppendChartContext.hCover old))
        (fun j => (AppendChartData.N input).obj j.1) (fun _ => Iso.refl _) T hST) :
    wordStageRetention G prior i S input old T hST := by
  let := wordSchemeSeparated G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
      prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G))))
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  obtain ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart,
    hmT, W, hfiniteW, haffW, V, hfiniteV, haffV, index, eV,
    hVcart, hVbase, hVold, hmodels⟩ := h
  let : IsProper baseT := hproper
  let : Smooth baseT := hsmooth
  refine ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart,
    hmT, W, hfiniteW, haffW, V, hfiniteV, haffV, index, eV,
    hVcart, hVbase, hVold, ?_⟩
  let d : AppendChartStage T hST old baseT mT :=
    @AppendChartStage.mk.{u} K kField kClosed kZero S G prior i T hST input old YT baseT mT
            qT hmT V hfiniteV haffV index eV hVold hVbase
  exact retain_word_cover G prior i T baseT mT hKcart W haffW hST old d hTcart hmodels

end ScalarStage


end SchubertGeometry
