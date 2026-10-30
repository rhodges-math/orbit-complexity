import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionModels
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordAppendSplitting
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframe retention through the append coefficient models

The original Borel charts and their polynomial cover are retained through the
coefficient models together with the word line and determinant sections.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private modelRetentionResult retain_model_coordinates from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionModels

namespace SchubertGeometry

open RetainedCharacter

universe u

open private initialCoefficient finalCoefficient polynomialSpecMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private borelPolynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendBorelCharts
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private coordinateScalarBase coordinateScalarMap
  fieldCoordinateCocone fieldCoordinateCocone_colimit
  fieldCoordinateDiagram_opens fieldCoordinateMap inverseCoordinates_affine
  retainedCoordinateRings singleCoordinateRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram from
  OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private map_exists_witness map_and_tail from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel

open private appendChartTriangle firstCoefficient firstChartIsos firstChartSquare firstChartBase
  scalarChartIsos scalarChartSquare scalarChartBase AppendChartData AppendChartContext
      AppendChartStage
  contextChartIsos contextRetentionData retain_chart_context fieldSchemeIso fieldSchemeIso_base
      fieldSchemeIso_left fieldSchemeMap fieldSchemeMap_comp from
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

private theorem with_section_family {I : Sort*} {A : I → Sort*}
    (E : ∀ i, A i) {P : ∀ i, A i → Prop} {Q : (∀ i, A i) → Prop}
    (hE : ∀ i, P i (E i)) (hQ : Q E) :
    ∃ F : (∀ i, A i), (∀ i, F i = E i) ∧ (∀ i, P i (F i)) ∧ Q F :=
  ⟨E, fun _ => rfl, hE, hQ⟩


open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

section CanonicalSections

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

variable
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)


private theorem with_canonical_word_sections
    (Q : (∀ n : ℕ,
      (Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n) ≅
        (Scheme.Modules.pullback q).obj
          (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word)) → Prop)
    (hQ : ∀ E, Q E) :
    ∃ E : ∀ n : ℕ,
      (Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n) ≅
        (Scheme.Modules.pullback q).obj
          (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word),
      (∀ n : ℕ, E n = retainedWordLineIso G F cF hcF word q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN n) ∧
      (∀ n : ℕ,
        (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
          (Scheme.Modules.pullback qN).map
            (retainedWordSection G F cF hcF word q point a ha beta hgroup hco hn
              N v hv deltaN hd P hP cN n) ≫ (E n).hom =
          (Scheme.Modules.pullbackObjUnitIso q).inv ≫
            (Scheme.Modules.pullback q).map
              (CharacterLine.wordDeterminantModuleSection G n word)) ∧ Q E := by
  let E := fun n => retainedWordLineIso G F cF hcF word q point a ha beta hgroup hco hn
    N v deltaN hd cN hcN qN hqN hcoN hnN n
  have hSections := fun n => retainedWordLineIso_section G F cF hcF word q point a ha beta
    hgroup hco hn N v deltaN hd cN hcN qN hqN hcoN hnN hv P hP n
  have family := with_section_family E
    (P := fun n en =>
      (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
        (Scheme.Modules.pullback qN).map
          (retainedWordSection G F cF hcF word q point a ha beta hgroup hco hn
            N v hv deltaN hd P hP cN n) ≫ en.hom =
        (Scheme.Modules.pullbackObjUnitIso q).inv ≫
          (Scheme.Modules.pullback q).map
            (CharacterLine.wordDeterminantModuleSection G n word))
    (Q := Q)
  exact family hSections (hQ E)

end CanonicalSections

open private selectedFrame selectedIndex from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent

section CoefficientPacket

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (i : G.rootBase.support) {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (psi : ∀ s, N.obj s → F.obj s) (H FG : Prop)
    (Tail : ∀ (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat),
      (∀ s, Function.Injective (v.app s).hom) →
      ∀ (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), (N.obj s)ˣ),
      (∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : N.obj s) =
        (wordTransitionUnit G F beta s j hj k hk : F.obj s)) →
      (∀ s j hj k hk l hl,
        delta s j hj l hl = delta s k hk l hl * delta s j hj k hk) →
      (∀ s t (f : s ⟶ t) j hj k hk,
        Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
          delta t j ((leOfHom f) hj) k ((leOfHom f) hk)) →
      ∀ P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s),
      (∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
        wordRingCoefficient G F point a j) → Prop)

private def coefficientTailResult : Prop :=
  H ∧ FG ∧
  ∃ (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (_hev : ∀ s x, (v.app s).hom x = psi s x)
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (hcoN : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (_hpoly : ∀ s, (P s).natDegree ≤ 2 ∧
      Polynomial.map (v.app s).hom (P s) =
        Polynomial.map (Spec.preimage (selectedFrame G F a s ≫
          flagChartMap G (point (selectedIndex s))).left).hom
            (DeterminantSection.simpleFramePolynomial G i
              (DeterminantSection.positiveDetCoefficient G)) ∧
      (v.app s).hom ((P s).coeff 2) =
        (Spec.preimage (selectedFrame G F a s ≫
          flagChartMap G (point (selectedIndex s))).left).hom
            (DeterminantSection.positiveDetCoefficient G) ∧
      ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n)
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j),
    (∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
          (delta s j hj k hk : N.obj s)) ∧
    Tail v hv delta hd hcoN hnN P hP

end CoefficientPacket

section WordStage

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (prior : List (@simpleRootIndex.{u} K kField kClosed kZero G))
    (i : @simpleRootIndex.{u} K kField kClosed kZero G) (S T R : Subalgebra ℤ K) (hST : S ≤ T) (hTR
        : T ≤ R)

variable [hSTFact : Fact (S ≤ T)] [hTRFact : Fact (T ≤ R)] [hSRFact : Fact (S ≤ R)]

private local instance appendAlgST : Algebra S T := (Subalgebra.inclusion (Fact.out : S ≤
    T)).toAlgebra
private local instance appendAlgTR : Algebra T R := (Subalgebra.inclusion (Fact.out : T ≤
    R)).toAlgebra
private local instance appendAlgSR : Algebra S R :=
  (Subalgebra.inclusion (Fact.out : S ≤ R)).toAlgebra
private local instance appendTowerSTK : IsScalarTower S T K :=
    Subalgebra.inclusion.isScalarTower_right (Fact.out : S ≤ T) K
private local instance appendTowerTRK : IsScalarTower T R K :=
    Subalgebra.inclusion.isScalarTower_right (Fact.out : T ≤ R) K
private local instance appendTowerSRK : IsScalarTower S R K :=
  Subalgebra.inclusion.isScalarTower_right (Fact.out : S ≤ R) K
private local instance appendTowerSTR : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _
    => rfl)

private def coefficientScalarValues {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    {J : Type u} (U : J → Y.Opens)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] ((@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) Y base {s : Finset J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))).obj s ≃ₐ[K] F.obj s) :
    ∀ s, (@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) R)
      (@appendAlgST.{u} K kField S T hSTFact)
      (@appendAlgTR.{u} K kField T R hTRFact) Y base J U).obj s → F.obj s :=
  let MT : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} T :=
    @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset J // s.Nonempty})) S T T
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra
          K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
          (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing
          K (@Field.toDivisionRing K kField))) T)
      (@appendAlgST.{u} K kField S T hSTFact)
      (inferInstanceAs (Algebra T T)) (@appendAlgST.{u} K kField S T hSTFact)
      (inferInstanceAs (IsScalarTower S T T)) (@intersectionCoordinates.{u,u,u} S
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
          {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
          (intersectionOpens U))
  fun s x => (@scalarDiagramComparison.{u,u,u} K kField S T hSTFact.out
    {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
        (@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) Y base {s : Finset J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)) F e s)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
        (AlgHom.id T (MT.obj s)) x)

variable {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (qK : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ Y)
    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    {input : @AppendChartData.{u} K kField kClosed kZero S₀ G prior i} (old :
        @AppendChartContext.{u} K kField kClosed kZero S₀ G prior i input)
    (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G prior i S hS₀ input old Y base qK)
    {J : Type u} (U : J → Y.Opens)


variable
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
          kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
          prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).map
          f).hom.toRingHom))]
    [hFdir : ((((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).op
          ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).op
          ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (hptF : cF.pt = Over.mk (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
        kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))))
    (q : cF.pt.left ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
        kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G))))))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
        kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a s j hj =
      chartLift G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K
        (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField
        kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj l hl =
      wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s k hk l hl * wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).map
          f).hom.toMonoidHom (wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk) =
        wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
            (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
            (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (e : ∀ s, K ⊗[S] ((@intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
          (intersectionOpens U))).obj s ≃ₐ[K] ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s)
    (he : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K (((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s) k *
        fieldCoordinateMap (S := S) (K := K) (Y := Y)
            (X := bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
                prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
                (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) base (bsdhToSpec
                G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
                (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
                (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK U s x)
    (v : ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
        (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)) ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
          (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) ⋙
          forget₂ (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, (v.app s).hom x =
      @coefficientScalarValues.{u} K kField S T R hSTFact hTRFact Y base J U
        ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
            (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
            kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) e s
          x)
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing
          K (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
          (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : ((@retainedCoordinateRings.{u} S T R
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
        (@appendAlgST.{u} K kField S T hSTFact) (@appendAlgTR.{u} K kField T R hTRFact) Y base J
        U)).obj s) =
      (wordTransitionUnit G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          beta s j hj k hk : ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))).obj
          s))
    (hcoN : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
          (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).map f).hom.toMonoidHom (delta s j hj
          k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (((@retainedCoordinateRings.{u} S T R
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
        (@appendAlgST.{u} K kField S T hSTFact) (@appendAlgTR.{u} K kField T R hTRFact) Y base J
        U)).obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
          (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
          point a j)

private def stageRetentionResult : Prop :=
  ∃ (hJ : Finite J) (hVfinite : Finite (AppendChartStage.V d).I₀) (hsm : Smooth base),
  let : Finite J := hJ
  let : Finite (AppendChartStage.V d).I₀ := hVfinite
  let : Smooth base := hsm
  ∃ (c₀ : Cocone ((singleCoordinateRings (S := S) (R := R) base U).op ⋙ algSpec (.of R))) (hpt₀ :
      c₀.pt = Over.mk (coordinateScalarBase (R := R) base)),
    let cN := retainedCoordinateCocone (S := S) (T := T) (R := R) ((@intersectionCoordinates.{u,u,u}
        S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
          (intersectionOpens U))) c₀
    ∃ _hcN : IsColimit cN,
      let qN := scalarModelProjection ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
          (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing
          K (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
          (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)) ((@intersectionCoordinates.{u,u,u} K
          (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) v
          cN cF hcF
      ∃ hCart : IsPullback qN cF.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      qN ≫ (eqToHom hpt₀).left ≫ (coordinateScalarMap (R := R) base) = (eqToHom hptF).left ≫ qK ∧
      ∃ (hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom
            (((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
                (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).map f).hom.toRingHom)))
        (hNdir : (((((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K
            Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ
            K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ
            K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
            (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField
            S T hSTFact) (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).op ⋙
          algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
            Scheme.forget).IsLocallyDirected)),
        let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
            (Spec.map (CommRingCat.ofHom
              (((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
                  (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                  (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                  (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                  (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                  (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                  (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
                  (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).map f).hom.toRingHom)) :=
                  hNopen
        let : (((((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
            (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).op ⋙
          algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
            Scheme.forget).IsLocallyDirected) := hNdir
        let hqN := scalarModelProjection_node
          ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
              (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
              (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
              (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
              (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
              (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
              (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
              (@appendAlgTR.{u} K kField T R hTRFact) Y base J U))
          ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
              (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
              (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
              (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))) v
          cN cF hcF
        ∃ ESections : ∀ n : ℕ,
            (Scheme.Modules.pullback qN).obj
              (matchingModule ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K
                  Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
                  (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
                  (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                  (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
                  T) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                  (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
                  R) (@appendAlgST.{u} K kField S T hSTFact) (@appendAlgTR.{u} K kField T R hTRFact)
                  Y base J U)) cN delta n) ≅
            (Scheme.Modules.pullback q).obj
              (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (@List.append.{u}
                  (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
                  (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
                  (@simpleRootIndex.{u} K kField kClosed kZero G))))),
          (∀ n : ℕ, ESections n = retainedWordLineIso G
            ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G
                (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
                (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
                (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
            cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
                (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
                (@simpleRootIndex.{u} K kField kClosed kZero G)))) q point a ha beta hgroup hco hn
            ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
                (@appendAlgTR.{u} K kField T R hTRFact) Y base J U))
            v delta hd cN _hcN qN hqN hcoN hnN n) ∧
          (∀ n : ℕ,
            (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
                (Scheme.Modules.pullback qN).map
                  (retainedWordSection G ((@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K
                      kField) (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
                      kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
                      i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U))))
                    cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
                        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
                        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) q point a
                        ha beta hgroup hco hn
                    ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K
                        Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
                        (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
                        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K
                        kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
                        K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                        (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T
                        hSTFact) (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)) v hv delta hd
                        P hP cN n) ≫
                  (ESections n).hom =
              (Scheme.Modules.pullbackObjUnitIso q).inv ≫
                (Scheme.Modules.pullback q).map
                  (CharacterLine.wordDeterminantModuleSection G n (@List.append.{u}
                      (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
                      (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
                      (@simpleRootIndex.{u} K kField kClosed kZero G)))))) ∧
          @modelRetentionResult.{u} K kField kClosed kZero G prior i S S₀ hS₀ input old
            Y base R (hST.trans hTR) J hJ
            ((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
                (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
                (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
                (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)) (@hNopen) hNdir cN _hcN
            (eqToIso hpt₀) delta hcoN hnN cF.pt.left cF.pt.hom qN q hCart
            (ESections 1) (fieldSchemeMap hptF qN)

omit [IsProper base] in
/-- The coefficient model of an appended word carries the canonical character-line
comparisons and determinant-section equations in every power. -/
theorem retained_word_sections (hq : (fieldSchemeIso hptF).hom = q) (hR : R.FG)
    (hdS : IsPullback (AppendChartStage.q d) base (AppendChartContext.base old)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hstage :
      let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
      matchingStageResult G base (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField
          kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
          (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK U cF hcF hptF
        (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
            kField kClosed kZero G)))) q point a ha beta hgroup hco hn v hv delta hd P hP
        (AppendChartStage.V d) (fun j => (firstCoefficient (A₁ := S) ((AppendChartData.N input).obj
            ((AppendChartStage.index d) j).1))) (AppendChartStage.eV d) Subtype.val_injective) :
    stageRetentionResult G prior i S T R hST hTR base qK hS₀ old d U cF hcF hptF
      q point a ha beta hgroup hco hn v hv delta hd hcoN hnN P hP := by
  let : Algebra (S₀) S := (Subalgebra.inclusion (hS₀)).toAlgebra
  apply map_exists_witness hstage
  intro hJ hstage
  apply map_exists_witness hstage
  intro hVfinite hstage
  apply map_exists_witness hstage
  intro hsm hstage
  let : Finite J := hJ
  let : Finite (AppendChartStage.V d).I₀ := hVfinite
  let : Smooth base := hsm
  apply map_exists_witness hstage
  intro c₀ hstage
  apply map_exists_witness hstage
  intro hpt₀ hstage
  apply map_exists_witness hstage
  intro hcN hstage
  apply map_exists_witness hstage
  intro hCart hstage
  apply map_and_tail hstage
  intro hproj hstage
  apply map_exists_witness hstage.2
  intro hNopen hstage
  apply map_exists_witness hstage
  intro hNdir hcoords
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
            (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
            (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).map f).hom.toRingHom)) := hNopen
  let : (((((@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
      (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)).op ⋙
    algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected) :=
    hNdir
  let MN : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R :=
    (@retainedCoordinateRings.{u} S T R (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) T) (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) R) (@appendAlgST.{u} K kField S T hSTFact)
        (@appendAlgTR.{u} K kField T R hTRFact) Y base J U)
  let FN : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K :=
    (@intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField) (bsdhScheme G (@List.append.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) prior (@List.cons.{u} (@simpleRootIndex.{u}
        K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G)))))
      (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (@inverseOpenDiagram.{u,u,u}
          Y (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G))))) qK {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) (intersectionOpens U)))
  let cN : Cocone (MN.op ⋙ algSpec (.of R)) :=
    retainedCoordinateCocone (S := S) (T := T) (R := R) ((@intersectionCoordinates.{u,u,u} S
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
          (intersectionOpens U))) c₀
  let qN : cF.pt.left ⟶ cN.pt.left := scalarModelProjection MN FN v cN cF hcF
  have hqN := scalarModelProjection_node MN FN v cN cF hcF
  have hproj' := hproj.trans (congrArg (· ≫ qK) (fieldSchemeIso_left hptF).symm)
  have family := with_canonical_word_sections (K := K) (R := R) (J := J)
    (hFopen := hFopen) (hFdir := hFdir) (hNopen := hNopen) (hNdir := hNdir)
    G FN cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) prior
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) q point a ha
    beta hgroup hco hn MN v delta hd cN hcN qN hqN hcoN hnN hv P hP
    (Q := fun EE =>
      @modelRetentionResult.{u} K kField kClosed kZero G prior i S S₀ hS₀ input old
        Y base R (hST.trans hTR) J hJ MN (@hNopen) hNdir cN hcN
        (eqToIso hpt₀) delta hcoN hnN cF.pt.left cF.pt.hom qN q hCart
        (EE 1) (fieldSchemeMap hptF qN))
  apply family
  intro ESections
  have factory := @retain_model_coordinates.{u} K kField kClosed kZero G prior i S S₀ hS₀
    input old Y base qK d R (hST.trans hTR) J hJ MN (@hNopen) hNdir cN hcN
    (eqToIso hpt₀) delta hcoN hnN cF.pt.left cF.pt.hom qN
    q hCart (ESections 1) (fieldSchemeIso hptF) (fieldSchemeMap hptF qN)
    (fieldSchemeIso_base hptF) hq hproj' hR hdS (fieldSchemeMap_comp hptF qN) hcoords
  exact factory



end WordStage


end SchubertGeometry
