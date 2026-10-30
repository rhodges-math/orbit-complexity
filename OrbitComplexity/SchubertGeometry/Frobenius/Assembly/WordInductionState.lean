import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordAppendSplitting
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
import OrbitComplexity.SchubertGeometry.Normality.Transitions.RefinedEndpointCharts
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Carried models for word induction

A prefix retains the diagrams, coefficients and boundaries produced by its
append step. Its singleton cover is derived from its field cocone.
The matching line and coefficient section are derived from
these data, and a splitting is a separate property of the chosen model.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private appendChartTriangle AppendChartData AppendChartData.mk AppendChartData.N
  AppendChartData.I AppendChartData.F AppendChartData.e AppendChartStage.eV
  AppendChartContext AppendChartContext.D AppendChartContext.eP AppendChartContext.cD
  AppendChartContext.base AppendChartContext.m AppendChartStage AppendChartStage.q
  AppendChartStage.V AppendChartStage.affine AppendChartStage.index
  AppendChartData.V₀ AppendChartData.sel AppendChartData.g AppendChartData.a₀
  AppendChartData.c AppendChartData.hend AppendChartData.p from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

open private wordPolynomialData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private stageRings terminalRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates

open private chartCover chartNode chartIndex chartSource chartAppend chartProjection
  chartField from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendChartInputs
open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter

namespace SchubertGeometry.RetainedCharacter


/-- The chosen arithmetic model of a word, with the charts, coefficients and
omitted-letter data carried by the append producer. -/
structure PrefixModel {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) where
  /-- The retained coefficient stage. -/
  S : Subalgebra ℤ K
  hS : S.FG
  twoUnit : IsUnit (2 : S)
  /-- The index of the carried singleton charts. -/
  J : Type u
  finite : Finite J
  /-- The coordinate diagram over the field. -/
  F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K
  /-- The carried arithmetic coordinate diagram. -/
  N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S
  /-- The scalar comparison on each coordinate ring. -/
  e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s
  he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom
  fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))
  fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected
  nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))
  nDir : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
    Scheme.forget).IsLocallyDirected
  fp : ∀ s, Algebra.FinitePresentation S (N.obj s)
  smooth : ∀ s, Algebra.Smooth S (N.obj s)
  /-- The selected entry of each nonempty chart intersection. -/
  sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val}
  /-- The field cocone on the word scheme. -/
  b : F.op ⋙ algSpec (.of K) ⟶
    (Functor.const {s : Finset J // s.Nonempty}ᵒᵖ).obj
      (Over.mk (bsdhToSpec G word))
  /-- The colimit certificate for the field cocone. -/
  hb : IsColimit (Cocone.mk (Over.mk (bsdhToSpec G word)) b)
  /-- The chosen arithmetic cocone. -/
  cG : Cocone (N.op ⋙ algSpec (.of S))
  /-- The colimit certificate for the arithmetic cocone. -/
  hcG : IsColimit cG
  /-- The comparison from the word scheme into the arithmetic model. -/
  m₀ : bsdhScheme G word ⟶ cG.pt.left
  hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  hbmodel : ∀ s, (b.app (op s)).left ≫ m₀ =
    Spec.map (CommRingCat.ofHom
      ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
        (cG.ι.app (op s)).left
  proper : IsProper cG.pt.hom
  smoothModel : Smooth cG.pt.hom
  /-- Geometric connectedness of the word model over its coefficient scheme. -/
  connected : GeometricallyConnected cG.pt.hom
  /-- The retained translates of the opposite big cell. -/
  point : J → G.points
  /-- The retained endpoint maps in the singleton coordinate rings. -/
  a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
    (oppositeUnipotentVariety G).toOver
  ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
    (b.app (op (singletonIndex j))).left ≫
      (𝟙 (bsdhScheme G word) ≫ bsdhMap G word)
  /-- The retained Borel transitions between endpoint lifts. -/
  beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
    (k : J) (_ : k ∈ s.val),
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver
  hgroup : ∀ s j hj k hk,
    @chartLift.{u} K kField kClosed kZero G J F point a s j hj =
      @chartLift.{u} K kField kClosed kZero G J F point a s k hk *
        (beta s j hj k hk ≫ borelInclusion G)
  hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
    beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
      (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk
  hbeta : ∀ s j hj k hk l hl,
    beta s j hj l hl = beta s k hk l hl * beta s j hj k hk
  /-- The ring transformation from the arithmetic diagram to the field diagram. -/
  v : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
    F ⋙ forget₂ (CommAlgCat K) CommRingCat
  hv : ∀ s, Function.Injective (v.app s).hom
  eValue : ∀ s x, e s ((1 : K) ⊗ₜ[S] x) = (v.app s).hom x
  /-- The carried arithmetic character transition units. -/
  delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
    (k : J) (_ : k ∈ s.val), (N.obj s)ˣ
  hdelta : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : N.obj s) =
    (@wordTransitionUnit.{u} K kField kClosed kZero G J F beta s j hj k hk : F.obj s)
  hco : ∀ s j hj k hk l hl,
    delta s j hj l hl = delta s k hk l hl * delta s j hj k hk
  hn : ∀ s t (f : s ⟶ t) j hj k hk,
    Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
      delta t j ((leOfHom f) hj) k ((leOfHom f) hk)
  /-- The retained polynomial family on all intersection nodes. -/
  P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s)
  hP : ∀ s, (P s).natDegree ≤ 2
  hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
    (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
      (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
        (delta s j hj k hk : N.obj s)
  hCoefficient : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
    @wordRingCoefficient.{u} K kField kClosed kZero G J F point a j
  /-- The arithmetic omitted-letter models. -/
  boundaries : Fin word.length → Over cG.pt.left
  hclosed : ∀ k, IsClosedImmersion (boundaries k).hom
  /-- The comparison from each omitted-letter scheme into its model. -/
  nB : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶ (boundaries k).left
  hnB : ∀ k, IsPullback
    (@bsdhOmitMap.{u} K kField kClosed kZero G word k) (nB k) m₀ (boundaries k).hom

/-- The field cocone on the retained word scheme. -/
def PrefixModel.fieldCocone {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) : Cocone (M.F.op ⋙ algSpec (.of K)) :=
  @Cocone.mk.{u,u,u,u+1} {s : Finset M.J // s.Nonempty}ᵒᵖ
    (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}ᵒᵖ))
    (Over (Spec (.of K))) (inferInstanceAs (Category.{u} (Over (Spec (.of K)))))
    (M.F.op ⋙ algSpec (.of K)) (Over.mk (bsdhToSpec G word)) M.b

/-- The arithmetic evaluation maps commute with the retained field cocone. -/
theorem PrefixModel.evaluationLeg {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (s : {s : Finset M.J // s.Nonempty}) :
    Spec.map (M.v.app s) ≫ (M.cG.ι.app (op s)).left =
      ((@PrefixModel.fieldCocone.{u} K kField kClosed kZero G word M).ι.app (op s)).left ≫ M.m₀ :=
          by
  have hmap : CommRingCat.ofHom
      ((M.e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = M.v.app s := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (M.eValue s)
  exact (congrArg (fun f => Spec.map f ≫ (M.cG.ι.app (op s)).left) hmap).symm.trans
    (M.hbmodel s).symm

/-- A retained proper model over an affine coefficient scheme is separated. -/
theorem PrefixModel.isSeparated {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) : M.cG.pt.left.IsSeparated := by
  let : IsProper M.cG.pt.hom := M.proper
  constructor
  rw [← terminal.comp_from M.cG.pt.hom]
  infer_instance

/-- Extend the coefficient diagram of a prefix along its retained subalgebra inclusion. -/
def PrefixModel.scalarDiagram {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (T : Subalgebra ℤ K) (hMT : M.S ≤ T) :=
  (@fixedFibreDiagram.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
      Finset M.J // s.Nonempty}))
    M.S T T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom)
    (@Algebra.id T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T))
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom)
    (@IsScalarTower.right M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      (@CommSemiring.toSemiring T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T))
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom)) M.N)

/-- A coefficient extension of a prefix with its chosen model and polynomials. -/
structure PrefixScalarModel {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) where
  /-- The final coefficient extension chosen by the append construction. -/
  T : Subalgebra ℤ K
  /-- The inclusion into the final coefficient stage. -/
  hMT : M.S ≤ T
  /-- Finite generation of the final stage. -/
  hT : T.FG
  /-- The cocone of the final scalar diagram. -/
  cT : Cocone (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).op ⋙ algSpec
      (.of T))
  /-- The colimit certificate for the final scalar cocone. -/
  hcT : IsColimit cT
  /-- The projection from the final scalar model. -/
  qT : cT.pt.left ⟶ M.cG.pt.left
  /-- The final coefficient Cartesian square. -/
  hqT : IsPullback qT cT.pt.hom M.cG.pt.hom
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMT).toRingHom))
  /-- The field comparison into the final model. -/
  mT : bsdhScheme G word ⟶ cT.pt.left
  /-- The field fibre of the final scalar model. -/
  hmT : IsPullback mT (bsdhToSpec G word) cT.pt.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T K)))
  /-- The comparison with the M-final field model. -/
  hmTComp : mT ≫ qT = M.m₀
  /-- The scalar projection on every affine node. -/
  hLeg : ∀ s, (cT.ι.app (op s)).left ≫ qT =
    Spec.map (((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N)).app s) ≫ (M.cG.ι.app (op s)).left
  /-- The open transition morphisms of the final diagram. -/
  nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T
        hMT)).map f).hom.toRingHom))
  /-- The directedness certificate of the final affine diagram. -/
  nDir : ((((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).op ⋙ algSpec
      (.of T) ⋙ Over.forget (Spec (.of T))) ⋙
    Scheme.forget).IsLocallyDirected
  /-- Finite presentation of the final coordinate rings. -/
  fp : ∀ s, Algebra.FinitePresentation T (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G
      word M T hMT)).obj s)
  /-- Smoothness of the final coordinate rings. -/
  smooth : ∀ s, Algebra.Smooth T (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T
      hMT)).obj s)
  /-- Properness of the final model. -/
  proper : IsProper cT.pt.hom
  /-- Smoothness of the final model. -/
  smoothModel : Smooth cT.pt.hom
  /-- Naturality of the final scalar comparison. -/
  he : ∀ s t (f : s ⟶ t), (((@scalarDiagramComparison.{u,u,u} K kField M.S T hMT
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        M.N M.F M.e)) t).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (((@PrefixModel.scalarDiagram.{u} K kField kClosed
        kZero G word M T hMT)).map f).hom) =
      (M.F.map f).hom.comp (((@scalarDiagramComparison.{u,u,u} K kField M.S T hMT
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        M.N M.F M.e)) s).toAlgHom
  /-- The ring transformation on the final coefficient diagram. -/
  v : ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)) ⋙ forget₂ (CommAlgCat
      T) CommRingCat ⟶
    M.F ⋙ forget₂ (CommAlgCat K) CommRingCat
  /-- Injectivity of the final arithmetic-to-field maps. -/
  hv : ∀ s, Function.Injective (v.app s).hom
  /-- The values of the final scalar comparison on the original factor. -/
  eValue : ∀ s x, ((@scalarDiagramComparison.{u,u,u} K kField M.S T hMT
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        M.N M.F M.e)) s ((1 : K) ⊗ₜ[T] x) = (v.app s).hom x
  /-- The field comparison on the affine cocone legs. -/
  hbmodel : ∀ s, (M.b.app (op s)).left ≫ mT =
    Spec.map (CommRingCat.ofHom
      ((((@scalarDiagramComparison.{u,u,u} K kField M.S T hMT
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        M.N M.F M.e)) s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
        (cT.ι.app (op s)).left
  /-- The character transition equations at the final stage. -/
  hdelta : ∀ s j hj k hk, (v.app s).hom
    (((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s j hj k hk : ((@PrefixModel.scalarDiagram.{u} K kField
            kClosed kZero G word M T hMT)).obj s) =
      (@wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta
        s j hj k hk : M.F.obj s)
  /-- The cocycle equation for the mapped transition units. -/
  hco : ∀ s j hj k hk l hl,
    ((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s j hj l hl =
      ((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s k hk l hl * ((@matchingScalarUnits.{u} M.S T M.J
            (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s j hj k hk
  /-- The refinement equation for the mapped transition units. -/
  hn : ∀ s t (f : s ⟶ t) j hj k hk,
    Units.map (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).map
        f).hom.toMonoidHom (((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s j hj k hk) =
      ((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) t j ((leOfHom f) hj) k ((leOfHom f) hk)
  /-- The chosen polynomial family on the scalar diagram. -/
  P : ∀ s, Polynomial (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).obj
      s)
  /-- The degree bounds for the mapped polynomials. -/
  hP : ∀ s, (P s).natDegree ≤ 2
  /-- The matching equation for the mapped leading coefficients. -/
  hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
    (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).map (singletonArrow s
        j hj)).hom ((P (singletonIndex j)).coeff 2) =
      (((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)).map (singletonArrow
          s k hk)).hom ((P (singletonIndex k)).coeff 2) *
        (((@matchingScalarUnits.{u} M.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
            (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M T hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N) M.delta)) s j hj k hk : ((@PrefixModel.scalarDiagram.{u} K kField
            kClosed kZero G word M T hMT)).obj s)
  /-- The second coefficients are the scalar images of the preceding coefficients. -/
  hCoefficientImage : ∀ j, (P (singletonIndex j)).coeff 2 =
    (((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra M.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S T hMT).toRingHom) M.N)).app (singletonIndex j)).hom ((M.P (singletonIndex j)).coeff 2)
  /-- The leading coefficients in the field coordinate rings. -/
  hCoefficient : ∀ j, (v.app (singletonIndex j)).hom
    ((P (singletonIndex j)).coeff 2) =
      @wordRingCoefficient.{u} K kField kClosed kZero G M.J M.F M.point M.a j
  /-- The omitted-letter models on the final scalar stage. -/
  boundaries : Fin word.length → Over cT.pt.left
  /-- Closedness of the final omitted-letter models. -/
  hclosed : ∀ k, IsClosedImmersion (boundaries k).hom
  /-- The projections of the final omitted-letter models. -/
  qB : ∀ k, (boundaries k).left ⟶ (M.boundaries k).left
  /-- The scalar Cartesian squares for the omitted-letter models. -/
  hqB : ∀ k, IsPullback (boundaries k).hom (qB k)
    qT (M.boundaries k).hom
  /-- The field comparisons into the final omitted-letter models. -/
  nB : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶
    (boundaries k).left
  /-- The field Cartesian squares for the final omitted-letter models. -/
  hnB : ∀ k, IsPullback
    (@bsdhOmitMap.{u} K kField kClosed kZero G word k)
      (nB k) mT (boundaries k).hom

/-- Construct the prefix carried by a coefficient extension. -/
def PrefixScalarModel.prefix {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word}
    (h : @PrefixScalarModel.{u} K kField kClosed kZero G word M) :
    @PrefixModel.{u} K kField kClosed kZero G word := by
  have htwo : IsUnit (2 : h.T) := by
    simpa only [map_ofNat] using M.twoUnit.map (Subalgebra.inclusion h.hMT).toRingHom
  have hconnected : GeometricallyConnected h.cT.pt.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.hqT M.connected
  exact @PrefixModel.mk.{u} K kField kClosed kZero G word
    h.T h.hT htwo M.J M.finite M.F
    (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M h.T h.hMT)
    (@scalarDiagramComparison.{u,u,u} K kField M.S h.T h.hMT
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
        M.N M.F M.e)
    h.he M.fOpen M.fDir h.nOpen h.nDir
    h.fp h.smooth M.sel M.b M.hb
    h.cT h.hcT h.mT h.hmT h.hbmodel
    h.proper h.smoothModel hconnected M.point M.a M.ha
    M.beta M.hgroup M.hnatural M.hbeta h.v h.hv h.eValue
    (@matchingScalarUnits.{u} M.S h.T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
    M.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M h.T h.hMT)
        (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s :
        Finset M.J // s.Nonempty}))
    M.S h.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
          (@RingHom.toAlgebra M.S h.T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S h.T h.hMT).toRingHom) M.N) M.delta) h.hdelta h.hco h.hn
    h.P
    h.hP h.hr h.hCoefficient
    h.boundaries h.hclosed h.nB h.hnB

/-- The trivialization of the next letter on the carried singleton cover.
The endpoint points and Borel transitions are those already in the prefix. -/
structure NextLetter {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (i : (@simpleRootIndex.{u} K kField kClosed kZero G)) where
  /-- The new-letter product chart on each carried singleton spectrum. -/
  c : ∀ j : M.J,
    (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j))) ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
            (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G)))))
  hchart : ∀ s j hj k hk,
    (((algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) ⊗ₘ 𝟙 (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c j =
    (overlapTwist (Y := (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) (M.beta s j hj k hk)).hom ≫
      (((algSpec (.of K)).map (M.F.map (singletonArrow s k hk)).op) ⊗ₘ 𝟙 _) ≫ c k
  hcart : ∀ s, IsPullback
    (fst ((algSpec (.of K)).obj (op (M.F.obj s)))
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
    ((((algSpec (.of K)).map (M.F.map (singletonArrow s (M.sel s).val (M.sel s).property)).op) ⊗ₘ 𝟙
        _) ≫ c (M.sel s).val).left
    (M.b.app (op s)).left (bsdhAppendFst G word i)
  hend : @appendChartTriangle.{u} K kField kClosed kZero G word i M.J
    (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) c M.point M.a

/-- Product charts for an appended letter, determined by the carried endpoint lifts. -/
noncomputable def PrefixModel.nextLetter {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (i : @simpleRootIndex.{u} K kField kClosed kZero G) :
    NextLetter M i := by
  classical
  have const_leg {C : Type u} {D : Type (u + 1)}
      [Category.{u} C] [Category.{u} D] (F : C ⥤ D) (X : D)
      (b : F ⟶ (Functor.const C).obj X) {s t : C} (f : s ⟶ t) :
      F.map f ≫ b.app t = b.app s := by
    exact (b.naturality f).trans (Category.comp_id (b.app s))
  have replace_base {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
      {h h' : Y ⟶ W} {k : Z ⟶ W} (H : IsPullback f g h k) (e : h = h') :
      IsPullback f g h' k := by
    cases e
    exact H
  have hOpen := (@retained_prior_charts.{u,u,u} K (@Field.toCommRing K kField)
    {s : Finset M.J // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
    (inferInstanceAs (Quiver.IsThin {s : Finset M.J // s.Nonempty}))
    (inferInstanceAs (Small.{u} {s : Finset M.J // s.Nonempty}))
    M.F M.fOpen M.fDir
    (Cocone.mk (Over.mk (bsdhToSpec G word)) M.b) M.hb).1
  have hFactor (j : M.J) :
      (M.a j).left ≫ flagSchemeChart G (M.point j) =
        (M.b.app (op (singletonIndex j))).left ≫ bsdhMap G word := by
    have h := (M.ha j).trans
      (congrArg (fun f => (M.b.app (op (singletonIndex j))).left ≫ f)
        (Category.id_comp (bsdhMap G word)))
    exact h
  have hData := fun j : M.J =>
    @bsdh_append_chart_endpoint.{u} K kField kClosed kZero G word i
      ((algSpec (.of K)).obj (op (M.F.obj (singletonIndex j))))
      (M.b.app (op (singletonIndex j))) (hOpen (singletonIndex j))
      (M.point j) (M.a j) (hFactor j)
  choose charts hCart _hChartOpen hEnd using hData
  have hLeg (s : {s : Finset M.J // s.Nonempty}) (j : M.J) (hj : j ∈ s.val) :
      (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op ≫
        M.b.app (op (singletonIndex j)) = M.b.app (op s) := by
    simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] using
      const_leg (M.F.op ⋙ algSpec (.of K)) (Over.mk (bsdhToSpec G word)) M.b
        (singletonArrow s j hj).op
  refine @NextLetter.mk.{u} K kField kClosed kZero G word M i ?_ ?_ ?_ ?_
  · exact charts
  · intro s j hj k hk
    have hpq := (hLeg s j hj).trans (hLeg s k hk).symm
    obtain ⟨β, hβ, htransition⟩ :=
      @bsdh_chart_transition.{u} K kField kClosed kZero G word i
        ((algSpec (.of K)).obj (op (M.F.obj (singletonIndex j))))
        ((algSpec (.of K)).obj (op (M.F.obj (singletonIndex k))))
        ((algSpec (.of K)).obj (op (M.F.obj s)))
        (M.b.app (op (singletonIndex j))) (M.b.app (op (singletonIndex k)))
        ((algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op)
        ((algSpec (.of K)).map (M.F.map (singletonArrow s k hk)).op) hpq
        (M.point j) (M.point k) (M.a j) (M.a k) (hFactor j) (hFactor k)
        (charts j) (charts k) (hCart j).w (hCart k).w (hEnd j) (hEnd k)
    have hmodel := M.hgroup s j hj k hk
    simp only [chartLift] at hmodel
    simp only [Category.assoc] at hβ
    have hmap : β ≫ borelInclusion G = M.beta s j hj k hk ≫ borelInclusion G :=
      mul_left_cancel (hβ.symm.trans hmodel)
    have hmono : Mono (borelInclusion G) := Over.mono_of_mono_left (borelInclusion G)
    have hβeq : β = M.beta s j hj k hk :=
      hmono.right_cancellation β (M.beta s j hj k hk) hmap
    exact hβeq ▸ htransition
  · intro s
    have hRefined := @refined_append_chart.{u} K kField kClosed kZero G word i
      ((algSpec (.of K)).obj (op (M.F.obj s)))
      ((algSpec (.of K)).obj (op (M.F.obj (singletonIndex (M.sel s).val))))
      (M.b.app (op (singletonIndex (M.sel s).val)))
      ((algSpec (.of K)).map
        (M.F.map (singletonArrow s (M.sel s).val (M.sel s).property)).op)
      (M.point (M.sel s).val) (M.a (M.sel s).val) (charts (M.sel s).val)
      (hCart (M.sel s).val) (hEnd (M.sel s).val)
    have hbase := congrArg (fun f => f.left)
      (hLeg s (M.sel s).val (M.sel s).property)
    simp only [Over.comp_left] at hbase
    exact replace_base hRefined.1 hbase
  · exact hEnd

/-- Construct the append charts on the two retained coefficient stages. -/
def NextLetter.scalarCharts {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} (L : NextLetter M
        i)
    (coefficients : PrefixScalarModel M) (prior : PrefixScalarModel coefficients.prefix) :
    AppendChartData prior.T G word i := by
  exact @AppendChartData.mk.{u} K kField kClosed kZero prior.T G word i M.J M.F
    (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T
        prior.hMT) prior.prefix.e M.sel
    (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j))))
    (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op)
    L.c M.point M.a L.hend (fun s => (M.b.app (op s)).left)
    (fun s => (M.b.app (op s)).w)

/-- On every prescribed field fibre, the canonical matching section normalizes
one raw functional which preserves every omitted-boundary kernel. -/
def PrefixSplits {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) : Prop :=
  ∀ (κ : Type u) [κComm : CommRing κ] (_hκField : IsField κ)
    (C : Type u) [cField : Field C] [_cκAlg : Algebra C κ] (pChar : ℕ)
    [cChar : ExpChar C pChar] [_cPerfect : PerfectRing C pChar]
    (_hp : Odd pChar) (_hp' : 1 < pChar)
    (coefficientMap : Spec (@CommRingCat.of κ κComm) ⟶ Spec (.of M.S))
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (@CommRingCat.of κ κComm))
    (x : X ⟶ M.cG.pt.left)
    (_hx : IsPullback x baseκ M.cG.pt.hom coefficientMap)
    (B : Fin word.length → Over X)
    (bD : ∀ j, (B j).left ⟶ (M.boundaries j).left)
    (_hB : ∀ j, IsPullback (B j).hom (bD j) x (M.boundaries j).hom),
    let L := @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta ((pChar - 1) / 2)
    let sectionHom := @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((pChar - 1) / 2)
    ∃ Theta : @frobeniusRestriction.{u} C (@Field.toCommRing C cField)
        pChar cChar X (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
        ((Scheme.Modules.pullback x).obj L) ⟶
          SheafOfModules.unit X.ringCatSheaf,
      Theta.app ⊤ (@Scheme.Modules.Hom.app.{u} X
        (SheafOfModules.unit X.ringCatSheaf) ((Scheme.Modules.pullback x).obj L)
        (@pullSection.{u} X M.cG.pt.left x L sectionHom) ⊤ (1 : Γ(X, ⊤))) =
          (1 : Γ(X, ⊤)) ∧
      ∀ j (V : X.Opens) (a : Γ(X, V)), (B j).hom.app V a = 0 →
        ∀ z : Γ((Scheme.Modules.pullback x).obj L, V),
          (B j).hom.app V (Theta.app V (a • z)) = 0

/-- The scalar stages, projective diagram and pre-final model of an append. -/
structure AppendGeometryBase {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} (L : NextLetter M
        i) : Type (u + 1) where
  /-- The chosen-root polynomial-retention stage. -/
  coefficients : PrefixScalarModel M
  /-- The scalar prefix model chosen by the append factory. -/
  prior : PrefixScalarModel coefficients.prefix
  /-- The projective model indexed by the two retained scalar stages. -/
  old : @AppendChartContext.{u} K kField kClosed kZero prior.T G word i
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
  /-- The projective-node projections. -/
  π : (AppendChartContext.D old) ⟶ (AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed
      kZero G word M i L coefficients prior)).op ⋙ algSpec (.of prior.T) ⋙ Over.forget (Spec (.of
      prior.T))
  /-- The Cartesian transition property of the projections. -/
  hπ : π.Equifibered
  /-- The projections in projective coordinates. -/
  hπmap : ∀ s, π.app (op s) = ((AppendChartContext.eP old) s).hom ≫
    projectiveToSpec ((AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word
        M i L coefficients prior)).obj s) (ULift.{u} (Fin 2))
  /-- The colimit certificate of the projective diagram. -/
  hcD : IsColimit (AppendChartContext.cD old)
  /-- The append projection over the retained prior model. -/
  qAppend : (AppendChartContext.cD old).pt ⟶ prior.cT.pt.left
  /-- The field square for the append projection. -/
  hAppend : IsPullback (AppendChartContext.m old) (bsdhAppendFst G word i)
    qAppend prior.mT
  /-- The structure morphism of the projective model. -/
  hAppendBase : AppendChartContext.base old = qAppend ≫ prior.cT.pt.hom
  /-- The projections on the projective-node legs. -/
  hleg : ∀ s, (AppendChartContext.cD old).ι.app (op s) ≫ qAppend =
    π.app (op s) ≫ (prior.cT.ι.app (op s)).left
  /-- The projective transition scaling units. -/
  a₀ : ∀ {s t}, (s ⟶ t) → ((AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
      word M i L coefficients prior)).obj t)ˣ
  /-- The projective transition translation coefficients. -/
  b₀ : ∀ {s t}, (s ⟶ t) → (AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
      word M i L coefficients prior)).obj t
  /-- The projective transition equations. -/
  hD : ∀ {s t} (f : s ⟶ t), (AppendChartContext.D old).map f.op ≫ ((AppendChartContext.eP old)
      s).hom =
    ((AppendChartContext.eP old) t).hom ≫ (projectiveLineScalingIso (a₀ f)).hom ≫
      (projectiveLineTranslationIso (b₀ f)).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) ((AppendChartData.N (@NextLetter.scalarCharts.{u} K
            kField kClosed kZero G word M i L coefficients prior)).map f).hom.toRingHom
  /-- The new-word model before the final scalar extension. -/
  pre : PrefixModel G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G))))
  /-- The inclusion into the pre-final new-word stage. -/
  hTpre : prior.T ≤ pre.S

/-- The retained polynomial charts, character comparisons and boundaries of an append. -/
structure AppendGeometry {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} (L : NextLetter M
        i)
    : Type (u + 1) extends @AppendGeometryBase.{u} K kField kClosed kZero G word M i L where
  /-- The polynomial cover indexed by this projective context. -/
  d : @AppendChartStage.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
    (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior) old
        pre.cG.pt.left pre.cG.pt.hom pre.m₀
  /-- The scalar square of the polynomial-cover stage. -/
  hd : IsPullback (AppendChartStage.q d) pre.cG.pt.hom (AppendChartContext.base old)
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTpre).toRingHom))
  /-- The chosen-root polynomial comparison on the retained prior diagram. -/
  hRoot : @wordPolynomialData.{u} K kField kClosed kZero G M.J M.F M.point M.a i
    prior.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) prior.T)
          (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T
          prior.hMT) prior.v prior.P
  /-- The arithmetic omitted-last-letter section. -/
  δ₀ : prior.cT.pt.left ⟶ (AppendChartContext.cD old).pt
  /-- Closedness of the omitted-last-letter section. -/
  hδClosed : IsClosedImmersion δ₀
  /-- The append projection composed with its section. -/
  hδSection : δ₀ ≫ qAppend = 𝟙 prior.cT.pt.left
  /-- The section on each projective node. -/
  hδNode : ∀ s, projectiveLineSection ((AppendChartData.N (@NextLetter.scalarCharts.{u} K kField
      kClosed kZero G word M i L coefficients prior)).obj s) ⟨1⟩ ≫
    ((AppendChartContext.eP old) s).inv ≫ (AppendChartContext.cD old).ι.app (op s) =
      (prior.cT.ι.app (op s)).left ≫ δ₀
  /-- The comparisons of the earlier omitted-letter models. -/
  earlierMap : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val < word.length),
    (pre.boundaries k).left ⟶ (M.boundaries ⟨k.val, hk⟩).left
  /-- The Cartesian squares for the earlier omitted letters. -/
  hEarlier : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val < word.length),
    IsPullback (pre.boundaries k).hom (earlierMap k hk)
      (AppendChartStage.q d ≫ qAppend ≫ prior.qT ≫ coefficients.qT)
      (M.boundaries ⟨k.val, hk⟩).hom
  /-- The comparison of the last omitted-letter model. -/
  lastMap : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (_hk : k.val = word.length),
    (pre.boundaries k).left ⟶ prior.cT.pt.left
  /-- The Cartesian square for the omitted last letter. -/
  hLast : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val = word.length),
    IsPullback (pre.boundaries k).hom (lastMap k hk) (AppendChartStage.q d) δ₀
  /-- The retained matching-line comparisons in every degree. -/
  lineIso : ∀ n, (Scheme.Modules.pullback pre.m₀).obj
      (@matchingModule.{u} pre.S pre.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) pre.S) pre.N pre.cG pre.delta n) ≅
    (Scheme.Modules.pullback (𝟙 (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField
        kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))))).obj
      (@CharacterLine.wordCharacterModule.{u} K kField kClosed kZero G
        (G.positiveRootCharacter ^ n) (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero
            G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G)))))
  /-- The comparisons are the canonical character-line identifications. -/
  hlineIso : ∀ n, lineIso n = @retainedWordLineIso.{u} K kField kClosed kZero G pre.J pre.F
      (@pre.fOpen) pre.fDir (@PrefixModel.fieldCocone.{u} K kField kClosed kZero G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G)))) pre) pre.hb (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))) (𝟙 (bsdhScheme G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G))))))
      pre.point pre.a pre.ha pre.beta pre.hgroup (@section_character_laws.{u,u} K kField kClosed
          kZero G pre.J pre.F pre.beta pre.hnatural pre.hbeta).1 (@section_character_laws.{u,u} K
          kField kClosed kZero G pre.J pre.F pre.beta pre.hnatural pre.hbeta).2
      pre.S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) pre.S)
          pre.N (@pre.nOpen) pre.nDir
      pre.v pre.delta pre.hdelta pre.cG pre.hcG pre.m₀
      (@PrefixModel.evaluationLeg.{u} K kField kClosed kZero G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G)))) pre)
      pre.hco pre.hn n
  /-- The polynomial projections on the retained cover. -/
  πField : ∀ z, Spec (.of (Polynomial ((@chartField.{u} K kField kClosed kZero prior.T pre.S G word
      i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
      old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z))) ⟶ (@chartCover.{u} K kField kClosed kZero
      prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
      coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d).X z
  /-- The field maps on the retained polynomial charts. -/
  jK : ∀ z, Spec (.of (Polynomial ((@chartField.{u} K kField kClosed kZero prior.T pre.S G word i
      hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
      old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z))) ⟶ (@PrefixModel.fieldCocone.{u} K kField
      kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
      (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))) pre).pt.left
  /-- The field Cartesian squares on the retained cover. -/
  hV : ∀ z, IsPullback (πField z) (jK z) ((@chartCover.{u} K kField kClosed kZero prior.T pre.S G
      word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients
      prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d).f z) pre.m₀
  /-- The field charts retain the word projection. -/
  hword : ∀ z, jK z ≫ (𝟙 (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
      kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G)))))) =
    @projectiveLinePolynomialChart.{u} ((@chartField.{u} K kField kClosed kZero prior.T pre.S G word
        i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients
        prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z)
      (@CommAlgCat.commRing K (@Field.toCommRing K kField) ((@chartField.{u} K kField kClosed kZero
          prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M
          i L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z)) ((@chartIndex.{u} K
          kField kClosed kZero prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField
          kClosed kZero G word M i L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d)
          z) ≫
      @projectiveAppendChart.{u} K kField kClosed kZero G i ((@chartField.{u} K kField kClosed kZero
          prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M
          i L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z)
        ((@chartSource.{u} K kField kClosed kZero prior.T pre.S G word i hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
            old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z) (Over.mk (bsdhToSpec G (@List.append.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u}
            (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
            kField kClosed kZero G)))))) ((@chartProjection.{u} K kField kClosed kZero prior.T pre.S
            G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
            coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z) ((@chartAppend.{u} K
            kField kClosed kZero prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField
            kClosed kZero G word M i L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀
            d) z)
  /-- The polynomial projections in arithmetic coordinates. -/
  hπField : ∀ z, πField z = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (((@scalarDiagramComparison.{u,u,u} K kField prior.T pre.S hTpre
      {s : Finset (AppendChartData.I (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i
          L coefficients prior)) // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset (AppendChartData.I (@NextLetter.scalarCharts.{u} K
          kField kClosed kZero G word M i L coefficients prior)) // s.Nonempty}))
      (AppendChartData.N (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
          coefficients prior)) (AppendChartData.F (@NextLetter.scalarCharts.{u} K kField kClosed
          kZero G word M i L coefficients prior)) (AppendChartData.e (@NextLetter.scalarCharts.{u} K
          kField kClosed kZero G word M i L coefficients prior))) ((@chartNode.{u} K kField kClosed
          kZero prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G
          word M i L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d)
          z)).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫
      ((@AppendChartStage.eV.{u} K kField kClosed kZero prior.T G word i
        pre.S hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients
            prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).inv
  /-- The field chart structure maps. -/
  hjKb : ∀ z, jK z ≫ (@PrefixModel.fieldCocone.{u} K kField kClosed kZero G (@List.append.{u}
      (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K
      kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
      pre).pt.hom =
    Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial ((@chartField.{u} K kField kClosed kZero
        prior.T pre.S G word i hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i
        L coefficients prior) old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z))))
  /-- The chosen coframe coefficient stage. -/
  Q : Subalgebra ℤ K
  /-- The inclusion into the coframe stage. -/
  hRQ : pre.S ≤ Q
  /-- Finite generation of the coframe stage. -/
  hQ : Q.FG
  /-- The coframe equations on the retained cover and line comparison. -/
  hdata : @commonMatchingCoframeData.{u} K kField kClosed kZero G word i pre.S pre.J pre.finite
      pre.N (@pre.nOpen) pre.nDir pre.cG pre.hcG (@PrefixModel.isSeparated.{u} K kField kClosed
          kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))) pre) pre.delta pre.hco pre.hn
      (@PrefixModel.fieldCocone.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed
          kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) pre).pt.left
          (@PrefixModel.fieldCocone.{u} K kField kClosed kZero G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G)))) pre).pt.hom pre.m₀ pre.hm₀ (𝟙 (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed
          kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))))) (lineIso 1)
      (@AppendChartStage.V.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior) old
          pre.cG.pt.left pre.cG.pt.hom pre.m₀ d)
      (@AppendChartStage.affine.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior) old
          pre.cG.pt.left pre.cG.pt.hom pre.m₀ d)
      (fun z => (@AppendChartData.V₀.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val)
      (fun z => (@AppendChartData.g.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val)
      (fun z => (@AppendChartData.a₀.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val)
      (fun z => (@AppendChartData.c.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val)
      (fun z => (@AppendChartData.hend.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val)
      (fun z => (@AppendChartData.F.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)).obj
        ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
            old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1)
      (fun z => (@AppendChartData.p.{u} K kField kClosed kZero prior.T G word i
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
        ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
            old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).val
        ((@AppendChartData.sel.{u} K kField kClosed kZero prior.T G word i
            (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior))
          ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
              (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior)
              old pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).1).property)
      (fun z => ((@AppendChartStage.index.{u} K kField kClosed kZero prior.T G word i pre.S hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L coefficients prior) old
          pre.cG.pt.left pre.cG.pt.hom pre.m₀ d) z).2)
      πField jK Q hRQ

/-- The carried prior polynomials after the two append coefficient extensions. -/
def AppendGeometry.priorPolynomials {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} {L : NextLetter M
        i}
    (g : @AppendGeometry.{u} K kField kClosed kZero G word M i L)
    (T : Type u) [tComm : CommRing T] [sTAlg : Algebra g.pre.S T] :
    ∀ j : M.J, Polynomial ((@terminalRings.{u} K kField kClosed kZero
      g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L
        g.coefficients g.prior) T tComm sTAlg).obj (singletonIndex j)) :=
  @matchingScalarPolynomial.{u} g.pre.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          tComm (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior))
          (@terminalRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior)
          T tComm sTAlg) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) g.pre.S T (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          tComm sTAlg (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior))) (@matchingScalarPolynomial.{u} g.prior.T g.pre.S M.J (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word g.coefficients.prefix
          g.prior.T g.prior.hMT) (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
          g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior)) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) g.prior.T g.pre.S (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@RingHom.toAlgebra g.prior.T g.pre.S (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        g.prior.T g.pre.S g.hTpre).toRingHom) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero
            G word g.coefficients.prefix g.prior.T g.prior.hMT)) (fun j => g.prior.P (singletonIndex
            j)))

/-- The universal append functional on a prescribed scalar extension of the retained geometry. -/
def AppendGeometry.rawData {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} {L : NextLetter M
        i}
    (g : @AppendGeometry.{u} K kField kClosed kZero G word M i L)
    (T : Subalgebra ℤ K) (hpreT : g.pre.S ≤ T) {Y : Scheme.{u}}
    (baseT : Y ⟶ Spec (.of T)) (qT : Y ⟶ g.pre.cG.pt.left) : Prop :=
  @appendPriorStep.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
    (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) g.old
        g.pre.cG.pt.left g.pre.cG.pt.hom g.pre.m₀ g.d
    T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra g.pre.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        g.pre.S T hpreT).toRingHom) (fun n => @matchingModule.{u} g.pre.S g.pre.J
            (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          g.pre.N g.pre.cG g.pre.delta n) (fun n => @coefficientMatchingSection.{u} g.pre.S g.pre.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          g.pre.N g.pre.cG g.pre.delta (fun j => (g.pre.P (singletonIndex j)).coeff 2) g.pre.hr n)
          (@AppendGeometry.priorPolynomials.{u} K kField kClosed kZero G word M i L g T
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
          (@RingHom.toAlgebra g.pre.S T (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        g.pre.S T hpreT).toRingHom))
    Y baseT qT

/-- A retained append geometry with its final scalar model and universal functional. -/
structure AppendStep {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) {i : (@simpleRootIndex.{u} K kField kClosed kZero G)} (L : NextLetter M
        i) : Type (u + 1) where
  /-- The retained append geometry. -/
  geometry : @AppendGeometry.{u} K kField kClosed kZero G word M i L
  /-- The final scalar model returned by the append construction. -/
  output : PrefixScalarModel geometry.pre
  /-- The universal append functional on this final scalar model. -/
  rawStep : @AppendGeometry.rawData.{u} K kField kClosed kZero G word M i L geometry
    output.T output.hMT output.cT.pt.left output.cT.pt.hom output.qT

end SchubertGeometry.RetainedCharacter
