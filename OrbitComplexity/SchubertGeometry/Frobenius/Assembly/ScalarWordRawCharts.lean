import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RawInfinityIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorBoundary
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Raw Cartier coordinates on the prescribed scalar word fibre

The same scalar projective nodes and coframes construct the next raw Cartier
morphism. Its original chart equations are retained together with normalization
and agreement on entire projective nodes.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.OperatorSheaf
open scoped TensorProduct

open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private nodePolynomial polynomialLeg chartRaw from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private affinePolynomialMap projectiveRefinement from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private affineProjectiveMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveTransitions
open private coefficient nodeBase projectiveScalar_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
open private stageRings terminalRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private fieldRings fieldPolynomials
  fieldNodeBase scalarCoefficients line unitModule diagram_open nodes_cover
  projective_natural_chain spec_chain pullback_right_cast pullback_post_cast
  node_projection_chain node_projection_cast polynomial_node_old polynomial_node_base
  refinement_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting
open private normalizedOperator_eq operator_on_node from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeCartier
open private AppendChartData AppendChartData.I AppendChartData.N AppendChartData.sel
  AppendChartContext AppendChartStage AppendChartStage.q
  AppendChartContext.D AppendChartContext.eP AppendChartContext.cD AppendChartContext.base
  from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

namespace SchubertGeometry.RetainedCharacter

variable {K₀ : Type u} [kField : Field K₀] [kClosed : IsAlgClosed K₀] [kZero : CharZero K₀]
    {S₀ S : Subalgebra ℤ K₀} {G : ReductiveGroups.ReductiveGroupData K₀}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X₁ : Scheme.{u}} {base₁ : X₁ ⟶ Spec (.of S)}
    {m₁ : bsdhScheme G (word ++ [i]) ⟶ X₁}
    (d : @AppendChartStage.{u} K₀ kField kClosed kZero S₀ G word i S hS₀ input context X₁ base₁ m₁)
    {T κ : Type u} [tComm : CommRing T] [κComm : CommRing κ] [sTAlg : Algebra S T] [tκAlg : Algebra
        T κ]

variable {XT Xκ : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X₁)
    (baseκ : Xκ ⟶ Spec (.of κ)) (qκ : Xκ ⟶ XT)
    (L : ℕ → XT.Modules) (sectionHom : ∀ n, unitModule XT ⟶ L n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
        tComm sTAlg).obj (singletonIndex j)))
    {C : Type u} [Field C] [Algebra C κ] {p : ℕ} [ExpChar C p] [PerfectRing C p]
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input
          T κ tComm κComm sTAlg tκAlg).map f).hom.toRingHom))]
    [(((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
        tκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
        sTAlg tκAlg).op ⋙ algSpec (.of κ))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset ((AppendChartData.I input)) // s.Nonempty})
      (j : (AppendChartData.I input)) (_ : j ∈ s.val)
      (k : (AppendChartData.I input)) (_ : k ∈ s.val),
        ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).obj s)ˣ)
    (hco : ∀ s j hj k hk l hl, delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
          sTAlg tκAlg).map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hP : ∀ j, (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
        κComm sTAlg tκAlg Q j).natDegree ≤ 2)
    (hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
          tκAlg).map (singletonArrow s j hj)).hom
          ((@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q j).coeff 2) =
        ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).map (singletonArrow s k hk)).hom
          ((@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q k).coeff 2) * (delta s j hj k hk : _))
    (basePrior : cN.pt.left ⟶ Spec (.of C))
    (Θ : frobeniusRestriction C p basePrior
      (matchingModule (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
          κComm sTAlg tκAlg) cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (hnorm : Θ.app ⊤ ((Scheme.Modules.Hom.app
      (coefficientMatchingSection (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
          κ tComm κComm sTAlg tκAlg) cN delta
        (fun j => (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
            κComm sTAlg tκAlg Q j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

/-- The prescribed scalar word fibre carries its raw Cartier chart equations,
in the same coframes that construct its normalized splitting. -/
theorem scalarWord_raw_charts
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (((AppendChartData.N input)).map f).hom.toRingHom))]
    [((((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
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
    (hd : IsPullback (AppendChartStage.q d) base₁ ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hT : IsPullback qT baseT base₁ (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hκ : IsPullback qκ baseκ baseT (Spec.map (CommRingCat.ofHom (algebraMap T κ))))
    (hcD : IsColimit ((AppendChartContext.cD context)))
    (a₀ : ∀ {s t}, (s ⟶ t) → (((AppendChartData.N input)).obj t)ˣ)
    (b₀ : ∀ {s t}, (s ⟶ t) → ((AppendChartData.N input)).obj t)
    (hD : ∀ {s t} (f : s ⟶ t), ((AppendChartContext.D context)).map f.op ≫ ((AppendChartContext.eP
        context) s).hom =
      ((AppendChartContext.eP context) t).hom ≫ (projectiveLineScalingIso (a₀ f)).hom ≫
        (projectiveLineTranslationIso (b₀ f)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (((AppendChartData.N input)).map f).hom.toRingHom)
    (hdata : @appendStageCoordinateData.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input context
        X₁ base₁ m₁ d T tComm sTAlg XT baseT qT κ κComm tκAlg Xκ baseκ qκ L sectionHom Q)
    (hp : Odd p) (hp' : 1 < p) :
    let β : Xκ ⟶ ((AppendChartContext.cD context)).pt := qκ ≫ qT ≫ AppendChartStage.q d
    let LX := (Scheme.Modules.pullback qκ).obj (L ((p - 1) / 2))
    let mX := pullSection qκ (L ((p - 1) / 2)) (sectionHom ((p - 1) / 2))
    ∃ (Knode : ∀ s, line ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
        κComm sTAlg tκAlg).obj s) ⟶ Xκ)
      (hopen : ∀ s, IsOpenImmersion (Knode s)),
      let : ∀ s, IsOpenImmersion (Knode s) := hopen
      (∀ s, Knode s ≫ β = projectiveCoeffMap (ULift.{u} (Fin 2))
        ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
            sTAlg tκAlg).app s).hom ≫ ((AppendChartContext.eP context) s).inv ≫
          ((AppendChartContext.cD context)).ι.app (.op s)) ∧
      (∀ s, Knode s ≫ baseκ = @fieldNodeBase.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
          tComm κComm sTAlg tκAlg s) ∧
      (∀ x : Xκ, ∃ s y, Knode s y = x) ∧
      ∃ E : ∀ s j, (Scheme.Modules.pullback
          (polynomialLeg (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
              κComm sTAlg tκAlg) Knode s j)).obj LX ≅
        unitModule (Spec (.of (Polynomial ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i
            hS₀ input T κ tComm κComm sTAlg tκAlg).obj s)))),
      ∃ (ΘX : frobeniusRestriction C p
          (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ⟶ unitModule Xκ)
        (SX : SchemeSplitting Xκ p),
        (∀ s j, ΘX.over
            (polynomialLeg (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
                tComm κComm sTAlg tκAlg) Knode s j).opensRange =
          chartRaw (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg) cN hcN delta hco hn basePrior Θ
            ((AppendChartData.sel input)) Knode
            (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX E s j) ∧
        SX.toOperator = ProjectiveCartier.twistedSectionOperator
          (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ΘX
          ((mX.val.app (op ⊤)).hom (1 : Γ(Xκ, ⊤))) ∧
        ∀ s, SX.toOperator.openPullback (Knode s) =
          (retainedNodeSplitting (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
              κ tComm κComm sTAlg tκAlg) cN hcN delta hco hn
            (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
                sTAlg tκAlg Q) hP hr basePrior Θ hnorm hp s
            ((AppendChartData.sel input) s).1
            ((AppendChartData.sel input) s).2).toOperator := by
  classical
  let : Algebra S₀ S :=
    (Subalgebra.inclusion hS₀).toAlgebra
  let : Algebra S₀ κ :=
    ((algebraMap T κ).comp ((algebraMap S T).comp
      (Subalgebra.inclusion hS₀).toRingHom)).toAlgebra
  intro β LX mX
  obtain ⟨oldS, hS, oldT, hTold, hTbase, hTcart,
    Knode, hK, hKbase, hKcart, hopen, V, hfinite, haffine, index, eV,
    hVold, hVbase, hVchart, hall, hhalf⟩ := hdata
  let : ∀ s, IsOpenImmersion (Knode s) := hopen
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (((AppendChartContext.D context)).map f) :=
    diagram_open (AppendChartData.N input) ((AppendChartContext.D context)) π hπ
  let : (((AppendChartContext.D context)) ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective π hπ
      (fun f => (((AppendChartContext.D context)).map f).injective)
  have hglobalGrid : IsPullback β baseκ ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (algebraMap T κ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫
          Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion hS₀).toRingHom)) := by
    simpa only [β, Category.assoc] using (hκ.paste_horiz hT).paste_horiz hd
  have hglobal : IsPullback β baseκ ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ κ))) :=
    pullback_right_cast (spec_chain
      (Subalgebra.inclusion hS₀).toRingHom
      (algebraMap S T) (algebraMap T κ)) hglobalGrid
  have hbase₀ := projectiveCocone_node_base (AppendChartData.N input) ((AppendChartContext.D
      context))
    ((AppendChartContext.eP context)) ((AppendChartContext.cD context)) cG π hπmap qOld hleg
        ((AppendChartContext.base context)) hbaseOld
  have holdbase (s) : (((AppendChartContext.eP context) s).inv ≫ ((AppendChartContext.cD
      context)).ι.app (.op s)) ≫
      (AppendChartContext.base context) = projectiveToSpec ((AppendChartData.N input).obj s)
          (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S₀
          ((AppendChartData.N input).obj s))) := by
    rw [Category.assoc, hbase₀ s, Iso.inv_hom_id_assoc]
  have hcomp (s) :
      coefficient T κ ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T tComm
          sTAlg).obj s) ≫
        coefficient S T ((@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input).obj s) ≫
          coefficient S₀ S ((AppendChartData.N input).obj s) =
      projectiveCoeffMap (ULift.{u} (Fin 2)) ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S
          G word i hS₀ input T κ tComm κComm sTAlg tκAlg).app s).hom :=
    projective_natural_chain _ _ _ _
      (fixedScalarMap S₀ S (AppendChartData.N input))
      (fixedScalarMap S T (@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input))
      (fixedScalarMap T κ (@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
          tComm sTAlg)) s
  have hchain (s) : Knode s ≫ β =
      (coefficient T κ ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T tComm
          sTAlg).obj s) ≫
        coefficient S T ((@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input).obj s) ≫
          coefficient S₀ S ((AppendChartData.N input).obj s)) ≫
        ((AppendChartContext.eP context) s).inv ≫ ((AppendChartContext.cD context)).ι.app (.op s) :=
    node_projection_chain _ _ _ _ _ _
      (((AppendChartContext.eP context) s).inv ≫ ((AppendChartContext.cD context)).ι.app (.op s))
      (oldS s) (oldT s) (Knode s) (hS s) (hTold s) (hK s)
  have hOldFull (s) : Knode s ≫ β =
      projectiveCoeffMap (ULift.{u} (Fin 2)) ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S
          G word i hS₀ input T κ tComm κComm sTAlg tκAlg).app s).hom ≫
        ((AppendChartContext.eP context) s).inv ≫ ((AppendChartContext.cD context)).ι.app (.op s) :=
    node_projection_cast ((AppendChartContext.eP context) s).inv (((AppendChartContext.cD
        context)).ι.app (.op s))
      (hcomp s) (hchain s)
  have hcart (s) : IsPullback
      (projectiveCoeffMap (ULift.{u} (Fin 2)) ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S
          G word i hS₀ input T κ tComm κComm sTAlg tκAlg).app s).hom ≫ ((AppendChartContext.eP
          context) s).inv)
      (Knode s) (((AppendChartContext.cD context)).ι.app (.op s)) β := by
    have h := scalarNode_isPullback
      (coefficient S₀ S ((AppendChartData.N input).obj s))
      (coefficient S T ((@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input).obj s))
      (coefficient T κ ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T tComm
          sTAlg).obj s))
      _ _ _ _ _ _ _
      (projectiveScalar_square S₀ S ((AppendChartData.N input).obj s))
      (projectiveScalar_square S T ((@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
          input).obj s))
      (projectiveScalar_square T κ ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
          input T tComm sTAlg).obj s))
      ((AppendChartContext.eP context) s) (((AppendChartContext.cD context)).ι.app (.op s))
          ((AppendChartContext.base context)) β baseκ
      hglobalGrid (Knode s) (holdbase s) (hchain s) (hKbase s)
    exact pullback_post_cast ((AppendChartContext.eP context) s).inv (hcomp s) h
  have hcover : ∀ x : Xκ, ∃ s y, Knode s y = x :=
    nodes_cover (fun s => (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
        κComm sTAlg tκAlg).obj s) Knode V (fun v => index v) eV hVchart
  obtain ⟨E, hE⟩ := hhalf p hp
  let a : ∀ {s t}, (s ⟶ t) → ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
      tComm κComm sTAlg tκAlg).obj t)ˣ :=
    fun {_ t} f => Units.map ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
        input T κ tComm κComm sTAlg tκAlg).app t).hom.toMonoidHom (a₀ f)
  let b : ∀ {s t}, (s ⟶ t) → (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
      tComm κComm sTAlg tκAlg).obj t := fun {_ t} f => ((@scalarCoefficients.{u} K₀ kField kClosed
      kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg).app t).hom (b₀ f)
  have hDaff {s t} (f : s ⟶ t) :
      ((AppendChartContext.D context)).map f.op ≫ ((AppendChartContext.eP context) s).hom =
          ((AppendChartContext.eP context) t).hom ≫
        affineProjectiveMap ((AppendChartData.N input).map f).hom.toRingHom (a₀ f) (b₀ f) := hD f
  have htransition {s t} (f : s ⟶ t) :
      projectiveRefinement ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
          tComm κComm sTAlg tκAlg).map f).hom.toRingHom (a f) (b f) ≫ Knode s = Knode t := by
    have h := scalarAppend_projective_transition (AppendChartData.N input) (@fieldRings.{u} K₀
        kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg)
        (@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
        sTAlg tκAlg) ((AppendChartContext.D context))
      ((AppendChartContext.eP context)) ((AppendChartContext.cD context)) f (a₀ f) (b₀ f) (hDaff f)
      ((AppendChartContext.base context)) baseκ β hglobal (Knode s) (Knode t)
      (hOldFull s) (hOldFull t) (hKbase s) (hKbase t)
    exact (congrArg (fun g : line ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input
        T κ tComm κComm sTAlg tκAlg).obj t) ⟶ line ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G
        word i hS₀ input T κ tComm κComm sTAlg tκAlg).obj s) => g ≫ Knode s)
      (refinement_eq ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
          κComm sTAlg tκAlg).map f).hom.toRingHom (a f) (b f))).trans h
  have htriangle {s t} (f : s ⟶ t) : polynomialLeg (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G
      word i hS₀ input T κ tComm κComm sTAlg tκAlg) Knode t ⟨0⟩ =
      Spec.map (CommRingCat.ofHom
        (affinePolynomialMap ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
            tComm κComm sTAlg tκAlg).map f).hom.toRingHom (a f) (b f))) ≫
        polynomialLeg (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
            κComm sTAlg tκAlg) Knode s ⟨0⟩ := by
    have h := scalarAppend_chart_transition (AppendChartData.N input) (@fieldRings.{u} K₀ kField
        kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg) (@scalarCoefficients.{u}
        K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg)
        ((AppendChartContext.D context))
      ((AppendChartContext.eP context)) ((AppendChartContext.cD context)) f (a₀ f) (b₀ f) (hD f)
      ((AppendChartContext.base context)) baseκ β hglobal (polynomialLeg (@fieldRings.{u} K₀ kField
          kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg) Knode s ⟨0⟩)
      (polynomialLeg (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
          κComm sTAlg tκAlg) Knode t ⟨0⟩)
      (polynomial_node_old β ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
          input T κ tComm κComm sTAlg tκAlg).app s).hom
        (((AppendChartContext.eP context) s).inv ≫ ((AppendChartContext.cD context)).ι.app (.op s))
            (Knode s) (hOldFull s) ⟨0⟩)
      (polynomial_node_old β ((@scalarCoefficients.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
          input T κ tComm κComm sTAlg tκAlg).app t).hom
        (((AppendChartContext.eP context) t).inv ≫ ((AppendChartContext.cD context)).ι.app (.op t))
            (Knode t) (hOldFull t) ⟨0⟩)
      (polynomial_node_base baseκ (Knode s) (hKbase s) ⟨0⟩)
      (polynomial_node_base baseκ (Knode t) (hKbase t) ⟨0⟩)
    exact h.symm
  obtain ⟨ΘX, hraw, hcharts, hnormal⟩ := exists_retained_word_cartier
    (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg) cN
        hcN delta hco hn (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ
        tComm κComm sTAlg tκAlg Q) hP hr
    basePrior Θ hnorm ((AppendChartData.sel input))
    Knode (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX mX E hp hp'
    ((AppendChartContext.D context)) ((AppendChartContext.cD context)) hcD β
    (fun s => projectiveCoeffMap (ULift.{u} (Fin 2)) ((@scalarCoefficients.{u} K₀ kField kClosed
        kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg).app s).hom ≫
        ((AppendChartContext.eP context) s).inv)
    hcart hcover a b htransition htriangle hE
  let φ := ProjectiveCartier.twistedSectionOperator
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) LX ΘX
      ((mX.val.app (op ⊤)).hom (1 : Γ(Xκ, ⊤)))
  let SX := φ.toSplitting 1 hnormal
  have hSX : SX.toOperator = φ := normalizedOperator_eq φ hnormal
  refine ⟨Knode, hopen, hOldFull, hKbase, hcover, E, ΘX, SX, hraw, hSX, ?_⟩
  intro s
  exact (congrArg (fun ψ : SchemeFrobeniusMap Xκ p => ψ.openPullback (Knode s)) hSX).trans
    (operator_on_node (Knode s) φ _ (hcharts s))

end SchubertGeometry.RetainedCharacter
