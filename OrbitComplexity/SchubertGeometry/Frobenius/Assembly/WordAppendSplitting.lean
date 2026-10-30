import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordArithmeticSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendChartInputs
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The normalized append step on a retained word model

The preceding coefficient polynomial and the canonical next-word section
construct the next Cartier morphism on the prescribed scalar fibre. Its
polynomial chart equations retain the same coframes and raw morphism.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.OperatorSheaf
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private wordPolynomialData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private nodePolynomial polynomialLeg chartRaw from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private fieldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private stageRings terminalRings singletonPolynomial scalarWordPolynomial
  scalarWordPolynomial_node from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private fieldRings fieldPolynomials
  fieldNodeBase scalarCoefficients line unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting
open private AppendChartData AppendChartData.I AppendChartData.F AppendChartData.N
  AppendChartData.e AppendChartData.sel AppendChartData.V₀ AppendChartData.p
  AppendChartData.c AppendChartData.g AppendChartData.a₀ AppendChartData.hend
  AppendChartContext AppendChartContext.D AppendChartContext.eP AppendChartContext.cD
  AppendChartContext.base AppendChartStage AppendChartStage.q AppendChartStage.V
  AppendChartStage.finite AppendChartStage.affine AppendChartStage.index
  AppendChartStage.eV AppendChartStage.hold AppendChartStage.hbase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

open private chartCover chartNode chartIndex chartChoice chartSource
  chartPoint chartEndpoint chartAppend chartTriangle chartProjection chartRing chartField
  chart_finite chart_affine from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendChartInputs

namespace SchubertGeometry.RetainedCharacter


/-- The indices of the simple roots selected by the Borel subgroup. -/
def simpleRootIndex {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) : Type u :=
  G.rootBase.support

section RawResult
variable {K₀ : Type u} [rawField : Field K₀] [rawClosed : IsAlgClosed K₀] [rawZero : CharZero K₀]
    {S₀ S : Subalgebra ℤ K₀} {G : ReductiveGroups.ReductiveGroupData K₀}
    {word : List (@simpleRootIndex.{u} K₀ rawField rawClosed rawZero G)} {i : (@simpleRootIndex.{u}
        K₀ rawField rawClosed rawZero G)}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X₁ : Scheme.{u}} {base₁ : X₁ ⟶ Spec (.of S)}
    {m₁ : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K₀ rawField rawClosed rawZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K₀ rawField rawClosed rawZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K₀ rawField rawClosed rawZero G)))) ⟶ X₁}
    (d : @AppendChartStage.{u} K₀ rawField rawClosed rawZero S₀ G word i S hS₀ input context X₁
        base₁ m₁)
    {T κ : Type u} [rawTComm : CommRing T] [rawκComm : CommRing κ]
    [rawSTAlg : Algebra S T] [rawTκAlg : Algebra T κ]

variable {XT Xκ : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X₁)
    (baseκ : Xκ ⟶ Spec (.of κ)) (qκ : Xκ ⟶ XT)
    (L : ℕ → XT.Modules) (sectionHom : ∀ n, unitModule XT ⟶ L n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input
        T rawTComm rawSTAlg).obj (singletonIndex j)))
    {C : Type u} [rawCField : Field C] [rawCκAlg : Algebra C κ] {p : ℕ}
    [rawChar : ExpChar C p] [rawPerfect : PerfectRing C p]
    [rawOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀
          input T κ rawTComm rawκComm rawSTAlg rawTκAlg).map f).hom.toRingHom))]
    [rawDir : (((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
        rawκComm rawSTAlg rawTκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
        rawTComm rawκComm rawSTAlg rawTκAlg).op ⋙ algSpec (.of κ))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset ((AppendChartData.I input)) // s.Nonempty})
      (j : (AppendChartData.I input)) (_ : j ∈ s.val)
      (k : (AppendChartData.I input)) (_ : k ∈ s.val),
        ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
            rawκComm rawSTAlg rawTκAlg).obj s)ˣ)
    (hco : ∀ s j hj k hk l hl, delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
          rawκComm rawSTAlg rawTκAlg).map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hP : ∀ j, (@fieldPolynomials.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
        rawTComm rawκComm rawSTAlg rawTκAlg Q j).natDegree ≤ 2)
    (hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm rawκComm
          rawSTAlg rawTκAlg).map (singletonArrow s j hj)).hom
          ((@fieldPolynomials.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
              rawκComm rawSTAlg rawTκAlg Q j).coeff 2) =
        ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
            rawκComm rawSTAlg rawTκAlg).map (singletonArrow s k hk)).hom
          ((@fieldPolynomials.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
              rawκComm rawSTAlg rawTκAlg Q k).coeff 2) * (delta s j hj k hk : (@fieldRings.{u} K₀
              rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm rawκComm rawSTAlg
              rawTκAlg).obj s))
    (basePrior : cN.pt.left ⟶ Spec (.of C))
    (Θ : frobeniusRestriction C p basePrior
      (matchingModule (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
          rawTComm rawκComm rawSTAlg rawTκAlg) cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (hnorm : Θ.app ⊤ ((Scheme.Modules.Hom.app
      (coefficientMatchingSection (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀
          input T κ rawTComm rawκComm rawSTAlg rawTκAlg) cN delta
        (fun j => (@fieldPolynomials.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
            rawTComm rawκComm rawSTAlg rawTκAlg Q j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

/-- The normalized splitting retains its raw morphism and both chart equations. -/
def appendFibreRawData (hp : Odd p) : Prop :=
    let β : Xκ ⟶ ((AppendChartContext.cD context)).pt := qκ ≫ qT ≫ AppendChartStage.q d
    let LX := (Scheme.Modules.pullback qκ).obj (L ((p - 1) / 2))
    let mX := pullSection qκ (L ((p - 1) / 2)) (sectionHom ((p - 1) / 2))
    ∃ (Knode : ∀ s, line ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
        rawTComm rawκComm rawSTAlg rawTκAlg).obj s) ⟶ Xκ)
      (hopen : ∀ s, IsOpenImmersion (Knode s)),
      let : ∀ s, IsOpenImmersion (Knode s) := hopen
      (∀ s, Knode s ≫ β = projectiveCoeffMap (ULift.{u} (Fin 2))
        ((@scalarCoefficients.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
            rawκComm rawSTAlg rawTκAlg).app s).hom ≫ ((AppendChartContext.eP context) s).inv ≫
          ((AppendChartContext.cD context)).ι.app (.op s)) ∧
      (∀ s, Knode s ≫ baseκ = @fieldNodeBase.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀
          input T κ rawTComm rawκComm rawSTAlg rawTκAlg s) ∧
      (∀ x : Xκ, ∃ s y, Knode s y = x) ∧
      ∃ E : ∀ s j, (Scheme.Modules.pullback
          (polynomialLeg (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
              rawTComm rawκComm rawSTAlg rawTκAlg) Knode s j)).obj LX ≅
        unitModule (Spec (.of (Polynomial ((@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G
            word i hS₀ input T κ rawTComm rawκComm rawSTAlg rawTκAlg).obj s)))),
      ∃ (ΘX : frobeniusRestriction C p
          (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ⟶ unitModule Xκ)
        (SX : SchemeSplitting Xκ p),
        (∀ s j, ΘX.over
            (polynomialLeg (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T
                κ rawTComm rawκComm rawSTAlg rawTκAlg) Knode s j).opensRange =
          @chartRaw.{u} C κ ((AppendChartData.I input)) rawCField rawκComm rawCκAlg p rawChar
              rawPerfect
            (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
                rawκComm rawSTAlg rawTκAlg) rawOpen rawDir cN hcN delta hco hn basePrior Θ
            ((AppendChartData.sel input)) Xκ Knode hopen
            (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX E s j) ∧
        SX.toOperator = ProjectiveCartier.twistedSectionOperator
          (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ΘX
          ((mX.val.app (op ⊤)).hom (1 : Γ(Xκ, ⊤))) ∧
        ∀ s, SX.toOperator.openPullback (Knode s) =
          (@retainedNodeSplitting.{u} C κ ((AppendChartData.I input)) rawCField rawκComm rawCκAlg p
              rawChar rawPerfect
            (@fieldRings.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ rawTComm
                rawκComm rawSTAlg rawTκAlg) rawOpen rawDir cN hcN delta hco hn
            (@fieldPolynomials.{u} K₀ rawField rawClosed rawZero S₀ S G word i hS₀ input T κ
                rawTComm rawκComm rawSTAlg rawTκAlg Q) hP hr basePrior Θ hnorm hp s
            ((AppendChartData.sel input) s).1
            ((AppendChartData.sel input) s).2).toOperator

end RawResult

/-- One scalar word model with open directed charts, its two comparisons,
their structural equations, and its append-step result. -/
def appendStepModels {S T K : Type u}
    [modelSComm : CommRing S] [modelTComm : CommRing T] [modelKComm : CommRing K]
    [modelSTAlg : Algebra S T] [modelTKAlg : Algebra T K]
    {J : Type v} [modelCategory : Category.{w} J] (N : J ⥤ CommAlgCat.{u} S)
    (cN : Cocone (N.op ⋙ algSpec (.of S)))
    {YK : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (Result : ∀ {Y : Scheme.{u}}, (Y ⟶ Spec (.of T)) → (Y ⟶ cN.pt.left) → Prop) : Prop :=
  let NT := @fixedFibreDiagram.{u,v,w} J modelCategory S T T
    modelSComm modelTComm modelTComm modelSTAlg
    (@Algebra.id T (@CommRing.toCommSemiring T modelTComm)) modelSTAlg
    (@IsScalarTower.right S T (@CommRing.toCommSemiring S modelSComm)
      (@Ring.toSemiring T (@CommRing.toRing T modelTComm)) modelSTAlg) N
  (∀ {s t : Jᵒᵖ} (f : s ⟶ t),
    IsOpenImmersion (((NT.op ⋙ algSpec (.of T)).map f).left)) ∧
  ((((NT.op ⋙ algSpec (.of T)) ⋙ Over.forget (Spec (.of T))) ⋙
    Scheme.forget).IsLocallyDirected) ∧
  ∃ (cT : Cocone (NT.op ⋙ algSpec (.of T))) (q : cT.pt.left ⟶ cN.pt.left)
    (n : YK ⟶ cT.pt.left),
    Nonempty (IsColimit cT) ∧
    IsPullback q cT.pt.hom cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
    IsPullback n baseK cT.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
    n ≫ q = m ∧
    n ≫ cT.pt.hom = baseK ≫
      Spec.map (CommRingCat.ofHom (algebraMap T K)) ∧
    (∀ s, (cT.ι.app s).left ≫ q = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : N.obj s.unop →ₐ[S]
        T ⊗[S] N.obj s.unop).toRingHom) ≫ (cN.ι.app s).left) ∧
    Smooth cT.pt.hom ∧ cT.pt.left.IsSeparated ∧ Result cT.pt.hom q

private theorem singleton_scalar_power {R T J : Type u}
    [rComm : CommRing R] [tComm : CommRing T] [rTAlg : Algebra R T]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (Q : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val}) :
    (fun n s => (Polynomial.map (Algebra.TensorProduct.includeRight :
      N.obj s →ₐ[R] T ⊗[R] N.obj s).toRingHom (singletonPolynomial N Q sel s)) ^ n) =
    (fun n s => singletonPolynomial (@fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty}
        (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
        (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) R
        T T rComm tComm tComm rTAlg (@Algebra.id T (@CommRing.toCommSemiring T tComm)) rTAlg
        (@IsScalarTower.right R T (@CommRing.toCommSemiring R rComm) (@Ring.toSemiring T
        (@CommRing.toRing T tComm)) rTAlg) N)
      (@matchingScalarPolynomial.{u} R T J rComm tComm N (@fixedFibreDiagram.{u,u,u} {s : Finset J
          // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder
          (Finset J) (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s =>
          s.Nonempty))) R T T rComm tComm tComm rTAlg (@Algebra.id T (@CommRing.toCommSemiring T
          tComm)) rTAlg (@IsScalarTower.right R T (@CommRing.toCommSemiring R rComm)
          (@Ring.toSemiring T (@CommRing.toRing T tComm)) rTAlg) N)
        (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J
            // s.Nonempty} (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
            (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) R T rComm tComm rTAlg N) Q) sel s
            ^ n) := by
  funext n s
  exact congrFun (congrFun (scalarWordPolynomial_node (K := T) N Q sel) n) s

private theorem polynomial_family_transport {A : Type*} (P : A → Prop)
    (f g : A) (h : f = g) (hf : P f) : P g := by
  cases h
  exact hf

private theorem inverse_chart_base {C : Type*} [Category C] {A B X S : C}
    (E : A ≅ B) (f : A ⟶ X) (base : X ⟶ S) (p : B ⟶ S)
    (h : f ≫ base = E.hom ≫ p) : (E.inv ≫ f) ≫ base = p := by
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem arithmetic_scalar_power {R S T J : Type u}
    [rComm : CommRing R] [sComm : CommRing S] [tComm : CommRing T] [sTAlg : Algebra S T]
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (tau : M ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      N ⋙ forget₂ (CommAlgCat S) CommRingCat)
    (P : ∀ j, Polynomial (M.obj (singletonIndex j)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val}) :
    (fun n s => (Polynomial.map (Algebra.TensorProduct.includeRight :
      N.obj s →ₐ[S] T ⊗[S] N.obj s).toRingHom
        (arithmeticNodePolynomial M N tau P s (sel s).1 (sel s).2)) ^ n) =
    (fun n s => singletonPolynomial (@fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty}
        (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
        (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) S
        T T sComm tComm tComm sTAlg (@Algebra.id T (@CommRing.toCommSemiring T tComm)) sTAlg
        (@IsScalarTower.right S T (@CommRing.toCommSemiring S sComm) (@Ring.toSemiring T
        (@CommRing.toRing T tComm)) sTAlg) N)
      (@matchingScalarPolynomial.{u} S T J sComm tComm N (@fixedFibreDiagram.{u,u,u} {s : Finset J
          // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder
          (Finset J) (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s =>
          s.Nonempty))) S T T sComm tComm tComm sTAlg (@Algebra.id T (@CommRing.toCommSemiring T
          tComm)) sTAlg (@IsScalarTower.right S T (@CommRing.toCommSemiring S sComm)
          (@Ring.toSemiring T (@CommRing.toRing T tComm)) sTAlg) N)
        (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J
            // s.Nonempty} (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
            (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) S T sComm tComm sTAlg N)
            (@matchingScalarPolynomial.{u} R S J rComm sComm M N tau P)) sel s ^ n) := by
  exact @singleton_scalar_power.{u} S T J sComm tComm sTAlg N (@matchingScalarPolynomial.{u} R S J
      rComm sComm M N tau P) sel

/-- A normalized prior functional constructs the append splitting on every
prescribed scalar fibre, retaining its raw polynomial chart equations. -/
def appendPriorStep {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)} {i : (@simpleRootIndex.{u} K
        kField kClosed kZero G)}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X : Scheme.{u}} {base : X ⟶ Spec (.of S)}
    {m : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ X}
    (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i S hS₀ input context X base m)
    {T : Type u} [tComm : CommRing T] [sTAlg : Algebra S T]
    (L₀ : ℕ → X.Modules) (s₀ : ∀ n, unitModule X ⟶ L₀ n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        sTAlg).obj (singletonIndex j)))
    {XT : Scheme.{u}} (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X) : Prop :=
  let L := fun n => (Scheme.Modules.pullback qT).obj (L₀ n)
  let sectionHom := fun n => pullSection qT (L₀ n) (s₀ n)
  ∀ (κ : Type u) [κComm : CommRing κ] [tκAlg : Algebra T κ]
    (C : Type u) [cField : Field C] [cκAlg : Algebra C κ] (p : ℕ)
    [cChar : ExpChar C p] [cPerfect : PerfectRing C p]
    [fieldOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          T κ tComm κComm sTAlg tκAlg).map f).hom.toRingHom))]
    [fieldDir : (((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
        sTAlg tκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cPrior : Cocone ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
        κComm sTAlg tκAlg).op ⋙ algSpec (.of κ)))
    (hcPrior : IsColimit cPrior)
    (delta : ∀ (s : {s : Finset ((AppendChartData.I input)) // s.Nonempty})
      (j : (AppendChartData.I input)) (_ : j ∈ s.val) (k : (AppendChartData.I input)) (_ : k ∈
          s.val),
        ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).obj s)ˣ)
    (hco : ∀ s j hj k hk l hl, delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
          sTAlg tκAlg).map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hP : ∀ j, (@fieldPolynomials.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
        sTAlg tκAlg Q j).natDegree ≤ 2)
    (hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
          tκAlg).map (singletonArrow s j hj)).hom
          ((@fieldPolynomials.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q j).coeff 2) =
        ((@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).map (singletonArrow s k hk)).hom
          ((@fieldPolynomials.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q k).coeff 2) * (delta s j hj k hk : (@fieldRings.{u} K kField kClosed
              kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg).obj s))
    (basePrior : cPrior.pt.left ⟶ Spec (.of C))
    (Theta : frobeniusRestriction C p basePrior
      (matchingModule (@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
          κComm sTAlg tκAlg) cPrior delta ((p - 1) / 2)) ⟶
        unitModule cPrior.pt.left)
    (hnorm : Theta.app ⊤ ((Scheme.Modules.Hom.app
      (coefficientMatchingSection (@fieldRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T
          κ tComm κComm sTAlg tκAlg) cPrior delta
        (fun j => (@fieldPolynomials.{u} K kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
            κComm sTAlg tκAlg Q j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cPrior.pt.left, ⊤))) = (1 : Γ(cPrior.pt.left, ⊤)))
    (hp : Odd p) (_hp' : 1 < p)
    (Xκ : Scheme.{u}) (baseκ : Xκ ⟶ Spec (.of κ)) (qκ : Xκ ⟶ XT)
    (_hκ : IsPullback qκ baseκ baseT (Spec.map (CommRingCat.ofHom (algebraMap T κ)))),
    @appendFibreRawData.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d
      T κ tComm κComm sTAlg tκAlg XT Xκ qT baseκ qκ L sectionHom Q
      C cField cκAlg p cChar cPerfect fieldOpen fieldDir cPrior hcPrior delta hco hn
      hP hr basePrior Theta hnorm hp

private theorem append_step_sections
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)} {i : (@simpleRootIndex.{u} K
        kField kClosed kZero G)}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X : Scheme.{u}} {base : X ⟶ Spec (.of S)}
    {m : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ X}
    (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i S hS₀ input context X base m)
    [givenOldOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (((AppendChartData.N input)).map f).hom.toRingHom))]
    [givenOldDir : ((((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
      Over.forget (Spec (.of S₀))) ⋙ Scheme.forget).IsLocallyDirected]
    (cG : Cocone (((AppendChartData.N input)).op ⋙ algSpec (.of S₀)))
    (π : (AppendChartContext.D context) ⟶ ((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
      Over.forget (Spec (.of S₀)))
    (hπ : π.Equifibered)
    (hπmap : ∀ s, π.app (.op s) = ((AppendChartContext.eP context) s).hom ≫
      projectiveToSpec (((AppendChartData.N input)).obj s) (ULift.{u} (Fin 2)))
    (qOld : ((AppendChartContext.cD context)).pt ⟶ cG.pt.left)
    (hleg : ∀ s, ((AppendChartContext.cD context)).ι.app (.op s) ≫ qOld =
      π.app (.op s) ≫ (cG.ι.app (.op s)).left)
    (hbaseOld : (AppendChartContext.base context) = qOld ≫ cG.pt.hom)
    (hd : IsPullback (AppendChartStage.q d) base ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hcD : IsColimit ((AppendChartContext.cD context)))
    (a₀ : ∀ {s t}, (s ⟶ t) → (((AppendChartData.N input)).obj t)ˣ)
    (b₀ : ∀ {s t}, (s ⟶ t) → ((AppendChartData.N input)).obj t)
    (hD : ∀ {s t} (f : s ⟶ t), ((AppendChartContext.D context)).map f.op ≫ ((AppendChartContext.eP
        context) s).hom =
      ((AppendChartContext.eP context) t).hom ≫ (projectiveLineScalingIso (a₀ f)).hom ≫
        (projectiveLineTranslationIso (b₀ f)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (((AppendChartData.N input)).map f).hom.toRingHom)

    {T : Type u} [tComm : CommRing T] [sTAlg : Algebra S T] {XT : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X)
    (hT : IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (U : XT.OpenCover.{u}) [givenFiniteU : Finite U.I₀]
    (indexT : U.I₀ ≃ ((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base
        m d)).I₀)
    (eT : ∀ j, U.X j ≅ Spec (.of (Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word
        i hS₀ input T tComm sTAlg).obj
      ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d) (indexT
          j))))))
    (holdT : ∀ j, U.f j ≫ qT = (eT j).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight : (@stageRings.{u} K kField kClosed kZero S₀ S G word i
            hS₀ input).obj ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X
            base m d) (indexT j)) →ₐ[S]
          T ⊗[S] (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
              ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d)
              (indexT j))).toRingHom)) ≫
        (AppendChartStage.eV d (indexT j)).inv ≫ ((@chartCover.{u} K kField kClosed kZero S₀ S G
            word i hS₀ input context X base m d)).f (indexT j))
    (hbaseT : ∀ j, U.f j ≫ baseT = (eT j).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap T (Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          T tComm sTAlg).obj ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
          X base m d) (indexT j)))))))
    (L₀ : ℕ → X.Modules) (s₀ : ∀ n, unitModule X ⟶ L₀ n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        sTAlg).obj (singletonIndex j)))
    {XK Z : Scheme.{u}} (n : XK ⟶ XT) (r : XK ⟶ Z)
    (LK : ℕ → Z.Modules)
    (EL : ∀ degree, (Scheme.Modules.pullback n).obj
      ((Scheme.Modules.pullback qT).obj (L₀ degree)) ≅ (Scheme.Modules.pullback r).obj (LK degree))
    (W : XT.OpenCover.{u}) {I : Type u} (index : U.I₀ → I)
    (PK : I → Scheme.{u}) (g : ∀ i, PK i ⟶ XK) (c : ∀ i, PK i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ degree i, (Scheme.Modules.pullback (c i)).obj (LK degree) ≅ unitModule (PK i))
    (z : ∀ j, PK (index j) ⟶ U.X j)
    (hwhole : ∀ j, z j ≫ U.f j = g (index j) ≫ n)
    (hfamily : ∀ degree, @scalarPolynomialSectionFamily.{u} XT XK Z n r
      ((Scheme.Modules.pullback qT).obj (L₀ degree)) (LK degree) (EL degree)
      W U I index PK g c hc (Epoly degree) z hwhole (pullSection qT (L₀ degree) (s₀ degree))
      (fun j => (eT j).hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i
            hS₀ input T tComm sTAlg).obj
          ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d)
              (indexT j)))))).inv (sectionChartPolynomial (2 * degree)
            (singletonPolynomial (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input
                T tComm sTAlg) Q ((AppendChartData.sel input))
              ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d)
                  (indexT j)) ^ degree) ((@chartIndex.{u} K kField kClosed kZero S₀ S G word i hS₀
                  input context X base m d) (indexT j)).down)))) :
    @appendPriorStep.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d
      T tComm sTAlg L₀ s₀ Q XT baseT qT := by
  intro κ hκring hκalg C hCfield hCalg p hchar hperfect hopen hdir
    cPrior hcPrior delta hco hn hP hr basePrior Theta hnorm hp hp' Xκ baseκ qκ hκ
  have hcoords := @appendStage_word_coordinates.{u} K kField kClosed kZero S₀ S G word i hS₀ input
      context X
    base m d cG π hπmap qOld hleg hbaseOld hd T tComm sTAlg XT
    baseT qT hT U givenFiniteU indexT eT holdT hbaseT
    κ hκring hκalg Xκ XK Z baseκ qκ hκ n r
    (fun degree => (Scheme.Modules.pullback qT).obj (L₀ degree)) LK EL W I index PK g c hc Epoly z
    hwhole (fun degree => pullSection qT (L₀ degree) (s₀ degree)) Q hfamily
  exact @scalarWord_raw_charts.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d
    T κ tComm hκring sTAlg hκalg XT Xκ baseT qT baseκ qκ
    (fun degree => (Scheme.Modules.pullback qT).obj (L₀ degree))
    (fun degree => pullSection qT (L₀ degree) (s₀ degree)) Q
    C hCfield hCalg p hchar hperfect hopen hdir cPrior hcPrior delta hco hn hP hr
    basePrior Theta hnorm givenOldOpen givenOldDir
    cG π hπ hπmap qOld hleg hbaseOld hd hT hκ hcD a₀ b₀ hD hcoords hp hp'



/-- On a coherent retained append stage, the preceding polynomial producer
constructs the next normalized word splitting and its raw chart equations.
The scalar model is fixed before the field and character degree are chosen. -/
theorem exists_word_append_splitting
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [givenFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [givenFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) (i : (@simpleRootIndex.{u} K
        kField kClosed kZero G))
    (q : cF.pt.left ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (@List.append.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u}
          K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero
          G))))))
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
    (S : Subalgebra ℤ K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [givenNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [givenNdir : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hUnits : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

    [givenFiniteJ : Finite J] [givenNSep : cN.pt.left.IsSeparated] [givenNSmooth : Smooth cN.pt.hom]
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (PN : ∀ s, Polynomial (N.obj s))
    (hPN : ∀ j, (v.app (singletonIndex j)).hom ((PN (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)
    (hK : IsPullback qN cF.pt.hom cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))

    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    (input : AppendChartData S₀ G word i) (context : AppendChartContext input)
    (m₁ : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ cN.pt.left)
    (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i S hS₀ input context cN.pt.left
        cN.pt.hom m₁)
    [givenOldOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (((AppendChartData.N input)).map f).hom.toRingHom))]
    [givenOldDir : ((((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
      Over.forget (Spec (.of S₀))) ⋙ Scheme.forget).IsLocallyDirected]
    (cG : Cocone (((AppendChartData.N input)).op ⋙ algSpec (.of S₀)))
    (π : (AppendChartContext.D context) ⟶ ((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
      Over.forget (Spec (.of S₀)))
    (hπ : π.Equifibered)
    (hπmap : ∀ s, π.app (.op s) = ((AppendChartContext.eP context) s).hom ≫
      projectiveToSpec (((AppendChartData.N input)).obj s) (ULift.{u} (Fin 2)))
    (qOld : ((AppendChartContext.cD context)).pt ⟶ cG.pt.left)
    (hleg : ∀ s, ((AppendChartContext.cD context)).ι.app (.op s) ≫ qOld =
      π.app (.op s) ≫ (cG.ι.app (.op s)).left)
    (hbaseOld : (AppendChartContext.base context) = qOld ≫ cG.pt.hom)
    (hd : IsPullback (AppendChartStage.q d) cN.pt.hom ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hcD : IsColimit ((AppendChartContext.cD context)))
    (a₀ : ∀ {s t}, (s ⟶ t) → (((AppendChartData.N input)).obj t)ˣ)
    (b₀ : ∀ {s t}, (s ⟶ t) → ((AppendChartData.N input)).obj t)
    (hD : ∀ {s t} (f : s ⟶ t), ((AppendChartContext.D context)).map f.op ≫ ((AppendChartContext.eP
        context) s).hom =
      ((AppendChartContext.eP context) t).hom ≫ (projectiveLineScalingIso (a₀ f)).hom ≫
        (projectiveLineTranslationIso (b₀ f)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (((AppendChartData.N input)).map f).hom.toRingHom)

    {R₀ : Type u} [r₀Comm : CommRing R₀]
    (M : {s : Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i input)) //
        s.Nonempty} ⥤ CommAlgCat.{u} R₀)
    (v₀ : M ⋙ forget₂ (CommAlgCat R₀) CommRingCat ⟶
      ((@AppendChartData.F.{u} K kField kClosed kZero S₀ G word i input)) ⋙ forget₂ (CommAlgCat K)
          CommRingCat)
    (P₀ : ∀ s, Polynomial (M.obj s))
    (aPrior : ∀ j, (algSpec (.of K)).obj (op (((@AppendChartData.F.{u} K kField kClosed kZero S₀ G
        word i input)).obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (hpoly₀ : @wordPolynomialData.{u} K kField kClosed kZero G ((@AppendChartData.I.{u} K kField
        kClosed kZero S₀ G word i input)) ((@AppendChartData.F.{u} K kField kClosed kZero S₀ G word
        i input)) ((@AppendChartData.g.{u} K kField kClosed kZero S₀ G word i input)) aPrior i R₀
        r₀Comm M v₀ P₀)
    (hsingle : ∀ j, aPrior j =
      (@AppendChartData.p.{u} K kField kClosed kZero S₀ G word i input) (singletonIndex j) j
          (Finset.mem_singleton_self j) ≫ (@AppendChartData.a₀.{u} K kField kClosed kZero S₀ G word
          i input) j)
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (((@AppendChartData.F.{u} K kField kClosed kZero S₀ G word i input)).map
          f).op ≫ (@AppendChartData.p.{u} K kField kClosed kZero S₀ G word i input) s j hj =
        (@AppendChartData.p.{u} K kField kClosed kZero S₀ G word i input) t j ((leOfHom f) hj))
    (tau : M ⋙ forget₂ (CommAlgCat R₀) CommRingCat ⟶
      ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)) ⋙ forget₂ (CommAlgCat S)
          CommRingCat) :
    let kComm : CommRing K := @Field.toCommRing K kField
    let kRing : Ring K := @DivisionRing.toRing K (@Field.toDivisionRing K kField)
    let kSemi : CommSemiring K := @Semifield.toCommSemiring K (@Field.toSemifield K kField)
    let kSemiring : Semiring K := @CommSemiring.toSemiring K kSemi
    let zComm : CommRing ℤ := Int.instCommRing
    let zSemi : CommSemiring ℤ := Int.instCommSemiring
    let zAlg : Algebra ℤ K := @Ring.toIntAlgebra K kRing
    let sComm : CommRing S := @Subalgebra.toCommRing ℤ K zComm kComm zAlg S
    let sSemi : CommSemiring S := @Subalgebra.toCommSemiring ℤ K zSemi kSemi zAlg S
    let kSelf : Algebra K K := @Algebra.id K kSemi
    let sKAlg : Algebra S K := @Subalgebra.toAlgebra K ℤ K zSemi kSemi kSemiring zAlg kSelf S
    let kMonoid : Monoid K := @Semiring.toMonoid K kSemiring
    let kAction : MulAction K K := @Monoid.toMulAction K kMonoid
    let nextOrder : PartialOrder (Finset J) := @Finset.instPartialOrder J
    let nextPreorder : Preorder (Finset J) := @PartialOrder.toPreorder (Finset J) nextOrder
    let nextIndexPreorder : Preorder {s : Finset J // s.Nonempty} :=
      @Subtype.preorder (Finset J) nextPreorder (fun s => s.Nonempty)
    let nextCategory : Category.{u} {s : Finset J // s.Nonempty} :=
      @Preorder.smallCategory {s : Finset J // s.Nonempty} nextIndexPreorder
    let e₀ : ∀ s, K ⊗[S] ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)).obj s
        ≃ₐ[K] ((@AppendChartData.F.{u} K kField kClosed kZero S₀ G word i input)).obj s := by
      delta stageRings
      exact @scalarDiagramComparison.{u,u,u} K kField S₀ S hS₀
        {s : Finset (AppendChartData.I input) // s.Nonempty} (@Preorder.smallCategory {s : Finset
            (AppendChartData.I input) // s.Nonempty} (@Subtype.preorder (Finset (AppendChartData.I
            input)) (@PartialOrder.toPreorder (Finset (AppendChartData.I input))
            (@Finset.instPartialOrder (AppendChartData.I input))) (fun s => s.Nonempty)))
        (AppendChartData.N input) (AppendChartData.F input) (AppendChartData.e input)
    ∀ (lineIso : ∀ degree,
      (Scheme.Modules.pullback qN).obj (@matchingModule.{u} S J sComm N cN deltaN degree) ≅
        (Scheme.Modules.pullback q).obj
          (@CharacterLine.wordCharacterModule.{u} K kField kClosed kZero G
            (G.positiveRootCharacter ^ degree) (@List.append.{u} (@simpleRootIndex.{u} K kField
                kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero
                G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))))
      (_hlineIso : ∀ degree, lineIso degree = @retainedWordLineIso.{u} K kField kClosed kZero G J F
          givenFopen givenFdir
      cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))) q point a ha beta hgroup hco hn S sComm N givenNopen givenNdir
      v deltaN hUnits cN hcN qN hqN hcoN hnN degree),
    let originalL := fun degree => @matchingModule.{u} S J sComm N cN deltaN degree
    let originalSection := fun degree => @retainedWordSection.{u} K kField kClosed kZero G J F
        givenFopen givenFdir cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero
        G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) q point a ha beta hgroup hco hn S sComm N
        v hv deltaN hUnits PN hPN cN degree
    ∀
    (_he₀ : ∀ s x, e₀ s ((1 : K) ⊗ₜ[S] (tau.app s).hom x) = (v₀.app s).hom x)
    (πField : ∀ z, Spec (.of (Polynomial (@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀
        input context cN.pt.left cN.pt.hom m₁ d z))) ⟶ (@chartCover.{u} K kField kClosed kZero S₀ S
        G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d).X z)
    (jK : ∀ z, Spec (.of (Polynomial (@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input
        context cN.pt.left cN.pt.hom m₁ d z))) ⟶ cF.pt.left)
    (_hV : ∀ z, IsPullback (πField z) (jK z) ((@chartCover.{u} K kField kClosed kZero S₀ S G word i
        hS₀ input context cN.pt.left cN.pt.hom m₁ d).f z) qN)
    (_hword : ∀ z, jK z ≫ q = @projectiveLinePolynomialChart.{u} (@chartField.{u} K kField kClosed
        kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d z) (@CommAlgCat.commRing K
        kComm (@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
        cN.pt.hom m₁ d z)) (@chartIndex.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
        cN.pt.left cN.pt.hom m₁ d z) ≫
      @projectiveAppendChart.{u} K kField kClosed kZero G i (@chartField.{u} K kField kClosed kZero
          S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d z) (@chartSource.{u} K kField
          kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d z) (Over.mk
          (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
          (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G)))))) (@chartProjection.{u} K kField
          kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d z)
          (@chartAppend.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
          cN.pt.hom m₁ d z))
    (_hπField : ∀ z, πField z = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ (@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d z)).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ ((@AppendChartStage.eV.{u} K kField
            kClosed kZero S₀ G word i S hS₀ input context cN.pt.left cN.pt.hom m₁ d) z).inv)
    (_hjKb : ∀ z, jK z ≫ cF.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (@chartField.{u} K kField kClosed kZero
          S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d z)))))
    (T : Subalgebra ℤ K) (hST : S ≤ T)

    (eNodes : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (_heNodes : ∀ (s : {s : Finset J // s.Nonempty}) (x : N.obj s),
      eNodes s ((1 : K) ⊗ₜ[S] x) = (v.app s).hom x)
    (_hqBase : q ≫ bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))) = cF.pt.hom)
    (_hdata : @commonMatchingCoframeData.{u} K kField kClosed kZero G word i S J givenFiniteJ
      N (@givenNopen) givenNdir cN hcN givenNSep deltaN hcoN hnN
      cF.pt.left cF.pt.hom qN hK q (lineIso 1)
      (@AppendChartStage.V.{u} K kField kClosed kZero S₀ G word i S hS₀ input context cN.pt.left
          cN.pt.hom m₁ d)
      (@AppendChartStage.affine.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
          cN.pt.left cN.pt.hom m₁ d)
      (fun z => (@AppendChartData.V₀.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val)
      (fun z => (@AppendChartData.g.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val)
      (fun z => (@AppendChartData.a₀.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val)
      (fun z => (@AppendChartData.c.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val)
      (fun z => (@AppendChartData.hend.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val)
      (fun z => (@AppendChartData.F.{u} K kField kClosed kZero S₀ G word i input).obj
        ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
            cN.pt.left cN.pt.hom m₁ d) z).1)
      (fun z => (@AppendChartData.p.{u} K kField kClosed kZero S₀ G word i input)
        ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
            cN.pt.left cN.pt.hom m₁ d) z).1
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).val
        ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
          ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
              cN.pt.left cN.pt.hom m₁ d) z).1).property)
      (fun z => ((@AppendChartStage.index.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
          cN.pt.left cN.pt.hom m₁ d) z).2)
      πField jK T hST),
    let tComm : CommRing T := @Subalgebra.toCommRing ℤ K zComm kComm zAlg T
    let tSemi : CommSemiring T := @Subalgebra.toCommSemiring ℤ K zSemi kSemi zAlg T
    let sTAlg : Algebra S T := @RingHom.toAlgebra S T sSemi tSemi
      (@Subalgebra.inclusion ℤ K zSemi kSemiring zAlg S T hST).toRingHom
    let tKAlg : Algebra T K := @Subalgebra.toAlgebra K ℤ K zSemi kSemi kSemiring zAlg kSelf T
    let _sTK : IsScalarTower S T K :=
      @Subalgebra.inclusion.isScalarTower_right ℤ K zSemi kSemiring zAlg S T hST K kAction
    let stageOrder : PartialOrder (Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word
        i input))) := @Finset.instPartialOrder ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G
        word i input))
    let stagePreorder : Preorder (Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i
        input))) :=
      @PartialOrder.toPreorder (Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i
          input))) stageOrder
    let stageIndexPreorder : Preorder {s : Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀
        G word i input)) // s.Nonempty} :=
      @Subtype.preorder (Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i input)))
          stagePreorder (fun s => s.Nonempty)
    let stageCategory : Category.{u} {s : Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀
        G word i input)) // s.Nonempty} :=
      @Preorder.smallCategory {s : Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word
          i input)) // s.Nonempty} stageIndexPreorder
    let Q₀ := @matchingScalarPolynomial.{u} R₀ S ((@AppendChartData.I.{u} K kField kClosed kZero S₀
        G word i input)) r₀Comm sComm M
      (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)
      tau (fun j => P₀ (singletonIndex j))
    let Q := @matchingScalarPolynomial.{u} S T ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G
        word i input)) sComm tComm
      (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)
      (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm sTAlg)
      (@fixedScalarMap.{u,u,u} {s : Finset ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word
          i input)) // s.Nonempty} stageCategory
        S T sComm tComm sTAlg
        (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)) Q₀
    @appendStepModels.{u,u,u} S T K sComm tComm kComm sTAlg tKAlg
      {s : Finset J // s.Nonempty} nextCategory N cN cF.pt.left cF.pt.hom qN
      (fun {Y : Scheme.{u}} (baseT : Y ⟶ Spec (.of T)) (qT : Y ⟶ cN.pt.left) =>
        @appendPriorStep.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
            cN.pt.hom m₁ d
          T tComm sTAlg originalL originalSection Q Y baseT qT) := by
  intro kComm kRing kSemi kSemiring zComm zSemi zAlg sComm sSemi kSelf sKAlg kMonoid kAction
    nextOrder nextPreorder nextIndexPreorder nextCategory e₀ lineIso hlineIso originalL
        originalSection
    he₀ πField jK hV hword hπField hjKb T hST eNodes heNodes hqBase hdata
    tComm tSemi sTAlg tKAlg sTK stageOrder stagePreorder stageIndexPreorder stageCategory Q₀ Q
  classical
  have hlineFamily := funext hlineIso
  subst lineIso
  have hVbase (z : ((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
      cN.pt.left cN.pt.hom m₁ d)).I₀) :
      (((@AppendChartStage.eV.{u} K kField kClosed kZero S₀ G word i S hS₀ input context cN.pt.left
          cN.pt.hom m₁ d) z).inv ≫ ((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d)).f z) ≫ cN.pt.hom =
        Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial ((@chartRing.{u} K kField kClosed
            kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z)))) :=
    @inverse_chart_base Scheme AlgebraicGeometry.Scheme.instCategory
      (((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
          m₁ d)).X z) (Spec (.of (Polynomial ((@chartRing.{u} K kField kClosed kZero S₀ S G word i
          hS₀ input context cN.pt.left cN.pt.hom m₁ d) z)))) cN.pt.left (Spec (.of S))
      ((@AppendChartStage.eV.{u} K kField kClosed kZero S₀ G word i S hS₀ input context cN.pt.left
          cN.pt.hom m₁ d) z) (((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d)).f z) cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial ((@chartRing.{u} K kField kClosed kZero
          S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z)))))
      ((@AppendChartStage.hbase.{u} K kField kClosed kZero S₀ G word i S hS₀ input context
          cN.pt.left cN.pt.hom m₁ d) z)
  have hmodels := @exists_word_arithmetic_sections.{u} K kField kClosed kZero G J F
    givenFopen givenFdir cF hcF word i q point a ha beta hgroup hco hn S N givenNopen givenNdir
    v deltaN hUnits cN hcN qN hqN hcoN hnN givenFiniteJ givenNSep givenNSmooth hv PN hPN hK
    (@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁
        d)
    (@chart_finite.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
        m₁ d)
    (@chart_affine.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
        m₁ d)
    R₀ ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i input)) r₀Comm M
    (@AppendChartData.F.{u} K kField kClosed kZero S₀ G word i input)
    v₀ P₀
    (@AppendChartData.g.{u} K kField kClosed kZero S₀ G word i input)
    aPrior hpoly₀
    (@AppendChartData.V₀.{u} K kField kClosed kZero S₀ G word i input)
    (@AppendChartData.a₀.{u} K kField kClosed kZero S₀ G word i input)
    (@AppendChartData.p.{u} K kField kClosed kZero S₀ G word i input)
    hsingle hpn
    (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)
    tau e₀ he₀
    (@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁
        d)
    (@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input)
    (@AppendChartData.c.{u} K kField kClosed kZero S₀ G word i input)
    (@AppendChartData.hend.{u} K kField kClosed kZero S₀ G word i input)
    (@chartIndex.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁
        d)
    πField jK hV hword T hST
    (@AppendChartStage.eV.{u} K kField kClosed kZero S₀ G word i S hS₀ input context cN.pt.left
        cN.pt.hom m₁ d)
    hVbase hπField hjKb eNodes heNodes hqBase hdata
  obtain ⟨hopen, hdir, cT, qT, n, hcT, hqT, hnativePB, hbase, hnbase, hlegs,
    hsmooth, hsep, hfiniteW, VT, hfiniteV, haffine, index, eVT, _hcart, hstruct,
    hold, _hcoord, hactual, _hnative, hsections⟩ := hmodels
  let WT := (@matchingSingletonCover.{u} S J sComm N givenNopen givenNdir cN hcN).pullback₂ qT
  let LK := fun degree => @CharacterLine.wordCharacterModule.{u} K kField kClosed kZero G
    (G.positiveRootCharacter ^ degree) (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed
        kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i
        (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
  let EL := fun degree =>
    ((pullbackComp n qT).app (originalL degree) ≪≫ (pullbackCongr hbase).app (originalL degree)) ≪≫
      @retainedWordLineIso.{u} K kField kClosed kZero G J F givenFopen givenFdir
      cF hcF (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u}
          (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
          kField kClosed kZero G)))) q point a ha beta hgroup hco hn S sComm N givenNopen givenNdir
      v deltaN hUnits cN hcN qN hqN hcoN hnN degree
  let leg := fun z => @projectiveLinePolynomialChart.{u} ((@chartField.{u} K kField kClosed kZero S₀
      S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z) (@CommAlgCat.commRing K kComm
      ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
      m₁ d) z)) ((@chartIndex.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
      cN.pt.hom m₁ d) z) ≫
    @projectiveAppendChart.{u} K kField kClosed kZero G i ((@chartField.{u} K kField kClosed kZero
        S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z) ((@chartSource.{u} K kField
        kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z) (Over.mk
        (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word
        (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G)))))) ((@chartProjection.{u} K kField kClosed
        kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z) ((@chartAppend.{u} K
        kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z)
  let Epoly := fun degree z => @appendPolynomialFrame.{u} K kField kClosed kZero G word i
    ((@chartSource.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
        m₁ d) z) ((@chartPoint.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
        cN.pt.hom m₁ d) z)
    ((@chartEndpoint.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom
        m₁ d) z) ((@chartAppend.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
        cN.pt.left cN.pt.hom m₁ d) z) ((@chartTriangle.{u} K kField kClosed kZero S₀ S G word i hS₀
        input context cN.pt.left cN.pt.hom m₁ d) z)
    ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁
        d) z) ((@chartProjection.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
        cN.pt.left cN.pt.hom m₁ d) z) degree ((@chartIndex.{u} K kField kClosed kZero S₀ S G word i
        hS₀ input context cN.pt.left cN.pt.hom m₁ d) z)
  let zmap := fun z =>
    @fieldMap.{u} S T K sComm tComm kComm sTAlg tKAlg sKAlg sTK
      (((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)).obj ((@chartNode.{u} K
          kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) (index
          z))) ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
          cN.pt.hom m₁ d) (index z))
      (@CommAlgCat.commRing S sComm (((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input)).obj ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
          cN.pt.left cN.pt.hom m₁ d) (index z))))
      (@CommAlgCat.commRing K kComm ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d) (index z)))
      (@CommAlgCat.algebra S sComm (((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input)).obj ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
          cN.pt.left cN.pt.hom m₁ d) (index z))))
      (@CommAlgCat.algebra K kComm ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d) (index z)))
      (e₀ ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
          cN.pt.hom m₁ d) (index z))) ≫ (eVT z).inv
  let hwhole := fun z => (hactual z).w
  let Fpoly := fun degree s =>
    (Polynomial.map (Algebra.TensorProduct.includeRight :
      ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)).obj s →ₐ[S] T ⊗[S]
          ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input)).obj s).toRingHom
      (arithmeticNodePolynomial M ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input))
          tau (fun j => P₀ (singletonIndex j))
        s ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input) s).1
            ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input) s).2)) ^ degree
  let Gpoly := fun degree s => singletonPolynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S
      G word i hS₀ input T tComm sTAlg)) Q ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G
      word i input)) s ^ degree
  let Claim := fun polys : ∀ _degree : ℕ, ∀ s, Polynomial (((@terminalRings.{u} K kField kClosed
      kZero S₀ S G word i hS₀ input T tComm sTAlg)).obj s) =>
    ∀ degree, @scalarPolynomialSectionFamily.{u} cT.pt.left cF.pt.left (bsdhScheme G
        (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u}
        (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G)))))
      n q ((Scheme.Modules.pullback qT).obj (originalL degree))
      (LK degree) (EL degree) WT VT ((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          context cN.pt.left cN.pt.hom m₁ d)).I₀ index (fun z => Spec (.of (Polynomial
          ((@chartField.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
          cN.pt.hom m₁ d) z))))
      jK leg hword (Epoly degree) zmap hwhole (pullSection qT (originalL degree) (originalSection
          degree))
      (fun z => (eVT z).hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial (((@terminalRings.{u} K kField kClosed kZero S₀ S G word
            i hS₀ input T tComm sTAlg)).obj
          ((@chartNode.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
              cN.pt.hom m₁ d) (index z)))))).inv
          (sectionChartPolynomial (2 * degree) (polys degree ((@chartNode.{u} K kField kClosed kZero
              S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) (index z)))
            ((@chartIndex.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left
                cN.pt.hom m₁ d) (index z)).down)))
  have hpower : Fpoly = Gpoly :=
    @arithmetic_scalar_power.{u} R₀ S T ((@AppendChartData.I.{u} K kField kClosed kZero S₀ G word i
        input))
      r₀Comm sComm tComm sTAlg M ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input))
          tau (fun j => P₀ (singletonIndex j))
      ((@AppendChartData.sel.{u} K kField kClosed kZero S₀ G word i input))
  have hsections' : Claim Gpoly := polynomial_family_transport Claim Fpoly Gpoly hpower hsections
  have hStep := @append_step_sections.{u} K kField kClosed kZero S₀ S G word i hS₀ input context
    cN.pt.left cN.pt.hom m₁ d givenOldOpen givenOldDir
    cG π hπ hπmap qOld hleg hbaseOld hd hcD a₀ b₀ hD
    T tComm sTAlg cT.pt.left cT.pt.hom qT hqT VT hfiniteV index eVT hold hstruct
    originalL originalSection Q cF.pt.left (bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K
        kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)
        i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) n q LK EL WT
    ((@chartCover.{u} K kField kClosed kZero S₀ S G word i hS₀ input context cN.pt.left cN.pt.hom m₁
        d)).I₀ index (fun z => Spec (.of (Polynomial ((@chartField.{u} K kField kClosed kZero S₀ S G
        word i hS₀ input context cN.pt.left cN.pt.hom m₁ d) z))))
    jK leg hword Epoly zmap hwhole hsections'
  exact ⟨hopen, hdir, cT, qT, n, ⟨hcT⟩, hqT, hnativePB, hbase, hnbase, hlegs, hsmooth, hsep, hStep⟩

end SchubertGeometry.RetainedCharacter
