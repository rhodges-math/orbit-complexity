import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordCover
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionCoefficients
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryModels
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FixedScalarComparison
import OrbitComplexity.SchubertGeometry.Normality.Bundles.BundleInfinityComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial coefficient models on the append atlas

The original Borel charts and their polynomial cover are retained through the
coefficient models together with the word line and determinant sections.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000
set_option maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private chart_comparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas

namespace SchubertGeometry

open RetainedCharacter

universe u v w

open private polynomialSpecIso polynomialSpecIso_hom polynomialSpecIso_inv cancel_old_coefficient cancel_inverse_coefficient cancel_base_coefficient cancel_polynomial_coefficient cancel_polynomial_base cancel_field_coefficient cancel_polynomial_field fixedFibreDiagram_smooth fixedFibreDiagram_smooth_twice map_quadratic_relations scalar_comparison_value coordinate_comparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons

open private initialCoefficient finalCoefficient oldCoefficient polynomialSpecMap polynomial_spec_comp from
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
  scalarChartIsos scalarChartSquare scalarChartBase AppendChartData AppendChartContext AppendChartStage
  contextChartIsos contextRetentionData retain_chart_context fieldSchemeIso fieldSchemeIso_base fieldSchemeIso_left from
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

open private wordStageRetention retain_word_scalar_stage from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordCover
open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels

open private wordCoverRetention coverCoefficientResult from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordCover
open private coefficientRetentionResult from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionWordStage
open private selectedIndex_mem from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private intersectionCoordinates_smooth from
  OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

private theorem retain_prefix_polynomials {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word) (i : (@simpleRootIndex.{u} K kField kClosed kZero G)) :
    ∃ h : @PrefixScalarModel.{u} K kField kClosed kZero G word M,
      @wordPolynomialData.{u} K kField kClosed kZero G M.J M.F M.point M.a i
        h.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M h.T h.hMT)
        h.v h.P := by
  have hcoF : ∀ s j hj k hk l hl,
      @wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta s j hj l hl =
        @wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta s k hk l hl *
          @wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta s j hj k hk := by
    intro s j hj k hk l hl
    apply Units.ext
    have h := congrArg (fun z : (M.N.obj s)ˣ => (M.v.app s).hom (z : M.N.obj s))
      (M.hco s j hj k hk l hl)
    simpa only [Units.val_mul, map_mul, M.hdelta] using h
  have hnF : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (M.F.map f).hom.toMonoidHom
        (@wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta s j hj k hk) =
      @wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
    intro s t f j hj k hk
    apply Units.ext
    have h := congrArg (fun z : (M.N.obj t)ˣ => (M.v.app t).hom (z : M.N.obj t))
      (M.hn s t f j hj k hk)
    have hf := congrArg (fun z :
        (M.N ⋙ forget₂ (CommAlgCat M.S) CommRingCat).obj s ⟶
          (M.F ⋙ forget₂ (CommAlgCat K) CommRingCat).obj t =>
        z.hom (M.delta s j hj k hk : M.N.obj s))
      (M.v.naturality f)
    change (M.v.app t).hom ((M.N.map f).hom (M.delta s j hj k hk : M.N.obj s)) =
      (M.F.map f).hom ((M.v.app s).hom (M.delta s j hj k hk : M.N.obj s)) at hf
    change (M.v.app t).hom ((M.N.map f).hom (M.delta s j hj k hk : M.N.obj s)) =
      (M.v.app t).hom (M.delta t j ((leOfHom f) hj) k ((leOfHom f) hk) : M.N.obj t) at h
    rw [hf, M.hdelta, M.hdelta] at h
    exact h
  have hcoefficients := @exists_word_induction_coefficients.{u} K kField kClosed kZero
    G M.J M.F M.fOpen M.fDir (Cocone.mk (Over.mk (bsdhToSpec G word)) M.b) M.hb
    word (𝟙 (bsdhScheme G word)) M.point M.a M.ha M.beta M.hgroup hcoF hnF
    M.finite i M.S M.hS M.N M.fp M.smooth M.e M.he M.delta
    (fun s j hj k hk => (M.eValue s (M.delta s j hj k hk)).trans (M.hdelta s j hj k hk))
    (fun j => (M.P (singletonIndex j)).coeff 2)
    (fun j => (M.eValue (singletonIndex j) ((M.P (singletonIndex j)).coeff 2)).trans
      (M.hCoefficient j))
  obtain ⟨R, hMR, data⟩ := hcoefficients
  let rAlg : Algebra M.S R := (Subalgebra.inclusion hMR).toAlgebra
  let rTower : IsScalarTower M.S R K := Subalgebra.inclusion.isScalarTower_right hMR K
  obtain ⟨v, hR, hfull, hvalue, hinjective, hdelta, hco, hn, P, hP, htop, hsingle, hmatch⟩ := data
  have he := @scalarDiagramComparison_natural.{u,u,u} K kField M.S R hMR
    {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) M.N M.F M.e M.he
  have heValue := @scalar_comparison_value.{u} K kField M.S R hMR {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
    M.N M.F M.e v hfull
  have hscalar := @exists_fixed_scalar_comparison.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
    (fun s t => @Preorder.subsingleton_hom {s : Finset M.J // s.Nonempty} (@Subtype.preorder (Finset M.J) (@PartialOrder.toPreorder (Finset M.J) (@Finset.instPartialOrder M.J)) (fun s => s.Nonempty)) s t) (small_self {s : Finset M.J // s.Nonempty})
    M.S R K (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R) (@Field.toCommRing K kField) rAlg (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) R) (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) M.S) rTower M.N
    (fun {_ _} f => M.nOpen f.unop) M.nDir M.cG M.hcG
    (bsdhScheme G word) (bsdhToSpec G word) M.m₀ M.hm₀
  obtain ⟨hopen, hdir, cR, qR, mR, ⟨hcR⟩, hqR, hmR, hmComp, hmBase, hlegs⟩ := hscalar
  have hmodel : ∀ s, (M.b.app (op s)).left ≫ mR =
      Spec.map (CommRingCat.ofHom (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) M.N M.F M.e) s).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫ (cR.ι.app (op s)).left := by
    intro s
    have hmap : Spec.map (CommRingCat.ofHom
        ((M.e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) =
        Spec.map (CommRingCat.ofHom
          (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
            {s : Finset M.J // s.Nonempty}
            (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
            M.N M.F M.e) s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : M.N.obj s →ₐ[M.S] R ⊗[M.S] M.N.obj s).toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      apply congrArg (fun f : M.N.obj s →+* M.F.obj s => Spec.map (CommRingCat.ofHom f))
      exact RingHom.ext (fun x => ((heValue s ((1 : R) ⊗ₜ[M.S] x)).trans (hvalue s x)).symm)
    have hb : (M.b.app (op s)).left ≫ bsdhToSpec G word =
        Spec.map (CommRingCat.ofHom (algebraMap K (M.F.obj s))) := (M.b.app (op s)).w
    have hc : (cR.ι.app (op s)).left ≫ cR.pt.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R
          ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s))) :=
      (cR.ι.app (op s)).w
    have hbase : Spec.map (CommRingCat.ofHom (algebraMap K (M.F.obj s))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) =
        Spec.map (CommRingCat.ofHom
          (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
            {s : Finset M.J // s.Nonempty}
            (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
            M.N M.F M.e) s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R
            ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s))) := by
      have hring : (algebraMap K (M.F.obj s)).comp (algebraMap R K) =
          (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
            {s : Finset M.J // s.Nonempty}
            (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
            M.N M.F M.e) s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).comp
              (algebraMap R ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s)) := by
        apply RingHom.ext
        intro x
        change algebraMap K (M.F.obj s) (algebraMap R K x) =
          (@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
            {s : Finset M.J // s.Nonempty}
            (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
            M.N M.F M.e) s ((1 : K) ⊗ₜ[R] algebraMap R
              ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) x)
        have hinc := (Algebra.TensorProduct.includeRight :
          ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) →ₐ[R]
            K ⊗[R] ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s)).commutes x
        have htower := IsScalarTower.algebraMap_apply R K
          (K ⊗[R] (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) x
        have hecomm := ((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
          {s : Finset M.J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) M.N M.F M.e) s).commutes
            (algebraMap R K x)
        exact ((congrArg (fun z => (@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
          {s : Finset M.J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) M.N M.F M.e) s z) hinc).trans
            ((congrArg (fun z => (@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
              {s : Finset M.J // s.Nonempty}
              (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) M.N M.F M.e) s z) htower).trans hecomm)).symm
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R K))
        (CommRingCat.ofHom (algebraMap K (M.F.obj s)))).symm.trans
          ((congrArg (fun f : R →+* M.F.obj s => Spec.map (CommRingCat.ofHom f)) hring).trans
            (Spec.map_comp
              (CommRingCat.ofHom (algebraMap R
                ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s)))
              (CommRingCat.ofHom (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
                {s : Finset M.J // s.Nonempty}
                (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
                M.N M.F M.e) s).toRingHom.comp
                  (Algebra.TensorProduct.includeRight :
                    ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) →ₐ[R]
                      K ⊗[R] ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s)).toRingHom))))
    apply hqR.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => (M.b.app (op s)).left ≫ z) hmComp).trans
          ((M.hbmodel s).trans
            ((congrArg (fun z => z ≫ (M.cG.ι.app (op s)).left) hmap).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun z => Spec.map (CommRingCat.ofHom
                    (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
                      {s : Finset M.J // s.Nonempty}
                      (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
                      M.N M.F M.e) s).toRingHom.comp
                        Algebra.TensorProduct.includeRight.toRingHom)) ≫ z)
                  (hlegs (op s)).symm).trans (Category.assoc _ _ _).symm)))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => (M.b.app (op s)).left ≫ z) hmBase).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) hb).trans
              (hbase.trans
                ((congrArg (fun z => Spec.map (CommRingCat.ofHom
                    (((@scalarDiagramComparison.{u,u,u} K kField M.S R hMR
                      {s : Finset M.J // s.Nonempty}
                      (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
                      M.N M.F M.e) s).toRingHom.comp
                        Algebra.TensorProduct.includeRight.toRingHom)) ≫ z) hc.symm).trans
                  (Category.assoc _ _ _).symm)))))
  let boundaries : Fin word.length → Over cR.pt.left :=
    fun k => Over.mk (pullback.fst qR (M.boundaries k).hom)
  let nB : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶ (boundaries k).left :=
    fun k => pullback.lift ((@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ mR)
      (M.nB k) (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun z => (@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ z)
            hmComp).trans (M.hnB k).w))
  have hboundary : ∀ k, IsPullback
      (@bsdhOmitMap.{u} K kField kClosed kZero G word k) (nB k) mR (boundaries k).hom := by
    intro k
    have hf : nB k ≫ pullback.fst qR (M.boundaries k).hom =
        (@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ mR := pullback.lift_fst _ _ _
    have hs : nB k ≫ pullback.snd qR (M.boundaries k).hom = M.nB k := pullback.lift_snd _ _ _
    have houter : IsPullback (@bsdhOmitMap.{u} K kField kClosed kZero G word k)
        (nB k ≫ pullback.snd qR (M.boundaries k).hom) (mR ≫ qR) (M.boundaries k).hom := by
      erw [hs, hmComp]
      exact M.hnB k
    exact houter.of_bot hf.symm (IsPullback.of_hasPullback qR (M.boundaries k).hom)
  have hfp : ∀ s, Algebra.FinitePresentation R ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) := by
    intro s
    let : Algebra.FinitePresentation M.S (M.N.obj s) := M.fp s
    change Algebra.FinitePresentation R (R ⊗[M.S] M.N.obj s)
    infer_instance
  have hsmooth : ∀ s, Algebra.Smooth R ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M R hMR).obj s) := by
    intro s
    let : Algebra.Smooth M.S (M.N.obj s) := M.smooth s
    change Algebra.Smooth R (R ⊗[M.S] M.N.obj s)
    infer_instance
  let result : @PrefixScalarModel.{u} K kField kClosed kZero G word M :=
    { T := R
      hMT := hMR
      hT := hR
      cT := cR
      hcT := hcR
      qT := qR
      hqT := hqR
      mT := mR
      hmT := hmR
      hmTComp := hmComp
      hLeg := fun s => hlegs (op s)
      nOpen := fun f => hopen f.op
      nDir := hdir
      fp := hfp
      smooth := hsmooth
      proper := MorphismProperty.of_isPullback hqR M.proper
      smoothModel := MorphismProperty.of_isPullback hqR M.smoothModel
      he := he
      v := v
      hv := hinjective
      eValue := heValue
      hbmodel := hmodel
      hdelta := hdelta
      hco := hco
      hn := hn
      P := P
      hP := fun s => (hP s).1
      hr := hmatch
      hCoefficientImage := htop
      hCoefficient := hsingle
      boundaries := boundaries
      hclosed := fun k => MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback qR (M.boundaries k).hom).flip (M.hclosed k)
      qB := fun k => pullback.snd qR (M.boundaries k).hom
      hqB := fun k => IsPullback.of_hasPullback qR (M.boundaries k).hom
      nB := nB
      hnB := hboundary }
  exact ⟨result, hP⟩

open private priorIndex lastIndex from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
open private indexTransport from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryModels

namespace RetainedCharacter

open private join_chart_squares join_chart_base cancel_polynomial_pair cancel_chart_iso cancel_chart_pair cancel_chart_base chart_factor_transport scalar_initial_coefficient scalar_polynomial_field scalar_field_chart_equation spec_square evaluation_base scalar_factor node_base_square boundary_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons

private theorem append_earlier_boundary_fields
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G} {L : NextLetter M i}
    (geometry : @AppendGeometryBase.{u} K kField kClosed kZero G word M i L)
    (d : @AppendChartStage.{u} K kField kClosed kZero geometry.prior.T G word i geometry.pre.S geometry.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L geometry.coefficients geometry.prior)
      geometry.old geometry.pre.cG.pt.left geometry.pre.cG.pt.hom geometry.pre.m₀)
    (hBefore : ∃ p : ∀ k : Fin word.length,
        (geometry.pre.boundaries (@priorIndex.{u} K kField kClosed kZero G word i k)).left ⟶
          (geometry.prior.boundaries k).left,
      ∀ k, IsPullback
        (geometry.pre.boundaries (@priorIndex.{u} K kField kClosed kZero G word i k)).hom (p k)
        (AppendChartStage.q d ≫ geometry.qAppend) (geometry.prior.boundaries k).hom) :
    ∃ earlierMap : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val < word.length),
        (geometry.pre.boundaries k).left ⟶ (M.boundaries ⟨k.val, hk⟩).left,
      ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val < word.length),
        IsPullback (geometry.pre.boundaries k).hom (earlierMap k hk)
          (AppendChartStage.q d ≫ geometry.qAppend ≫ geometry.prior.qT ≫
            geometry.coefficients.qT)
          (M.boundaries ⟨k.val, hk⟩).hom := by
  classical
  obtain ⟨pBefore, hBefore⟩ := hBefore
  have h : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val < word.length),
      ∃ p : (geometry.pre.boundaries k).left ⟶ (M.boundaries ⟨k.val, hk⟩).left,
        IsPullback (geometry.pre.boundaries k).hom p
          (AppendChartStage.q d ≫ geometry.qAppend ≫ geometry.prior.qT ≫
            geometry.coefficients.qT)
          (M.boundaries ⟨k.val, hk⟩).hom := by
    intro k hk
    let k₀ : Fin word.length := ⟨k.val, hk⟩
    have hindex : @priorIndex.{u} K kField kClosed kZero G word i k₀ = k := Fin.ext rfl
    have hpair :
        ∃ p : (geometry.pre.boundaries (@priorIndex.{u} K kField kClosed kZero G word i k₀)).left ⟶
            (M.boundaries k₀).left,
          IsPullback (geometry.pre.boundaries (@priorIndex.{u} K kField kClosed kZero G word i k₀)).hom p
            (AppendChartStage.q d ≫ geometry.qAppend ≫ geometry.prior.qT ≫
              geometry.coefficients.qT)
            (M.boundaries k₀).hom := by
      refine ⟨(pBefore k₀ ≫ geometry.prior.qB k₀) ≫ geometry.coefficients.qB k₀, ?_⟩
      have hpaste := ((hBefore k₀).paste_vert (geometry.prior.hqB k₀)).paste_vert
        (geometry.coefficients.hqB k₀)
      have hbase : ((AppendChartStage.q d ≫ geometry.qAppend) ≫ geometry.prior.qT) ≫
          geometry.coefficients.qT =
          AppendChartStage.q d ≫ geometry.qAppend ≫ geometry.prior.qT ≫
            geometry.coefficients.qT := by
        exact (Category.assoc (AppendChartStage.q d ≫ geometry.qAppend)
          geometry.prior.qT geometry.coefficients.qT).trans
          (Category.assoc (AppendChartStage.q d) geometry.qAppend
            (geometry.prior.qT ≫ geometry.coefficients.qT))
      exact hbase ▸ hpaste
    exact @indexTransport.{1,0} (Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length)
      (fun x => ∃ p : (geometry.pre.boundaries x).left ⟶ (M.boundaries k₀).left,
        IsPullback (geometry.pre.boundaries x).hom p
          (AppendChartStage.q d ≫ geometry.qAppend ≫ geometry.prior.qT ≫
            geometry.coefficients.qT)
          (M.boundaries k₀).hom)
      (@priorIndex.{u} K kField kClosed kZero G word i k₀) k hindex hpair
  choose earlierMap hEarlier using h
  exact ⟨earlierMap, hEarlier⟩

private theorem append_last_boundary_fields
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G} {L : NextLetter M i}
    (geometry : @AppendGeometryBase.{u} K kField kClosed kZero G word M i L)
    (d : @AppendChartStage.{u} K kField kClosed kZero geometry.prior.T G word i geometry.pre.S geometry.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L geometry.coefficients geometry.prior)
      geometry.old geometry.pre.cG.pt.left geometry.pre.cG.pt.hom geometry.pre.m₀)
    (δ₀ : geometry.prior.cT.pt.left ⟶
      (AppendChartContext.cD geometry.old).pt)
    (hLast : ∃ p : (geometry.pre.boundaries (@lastIndex.{u} K kField kClosed kZero G word i)).left ⟶
        geometry.prior.cT.pt.left,
      IsPullback (geometry.pre.boundaries (@lastIndex.{u} K kField kClosed kZero G word i)).hom p
        (AppendChartStage.q d) δ₀) :
    ∃ lastMap : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (_hk : k.val = word.length),
        (geometry.pre.boundaries k).left ⟶ geometry.prior.cT.pt.left,
      ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (hk : k.val = word.length),
        IsPullback (geometry.pre.boundaries k).hom (lastMap k hk)
          (AppendChartStage.q d) δ₀ := by
  classical
  obtain ⟨pLast, hLast⟩ := hLast
  have h : ∀ (k : Fin (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))).length) (_hk : k.val = word.length),
      ∃ p : (geometry.pre.boundaries k).left ⟶ geometry.prior.cT.pt.left,
        IsPullback (geometry.pre.boundaries k).hom p
          (AppendChartStage.q d) δ₀ := by
    intro k hk
    have hindex : @lastIndex.{u} K kField kClosed kZero G word i = k := Fin.ext hk.symm
    have hpair : ∃ p : (geometry.pre.boundaries (@lastIndex.{u} K kField kClosed kZero G word i)).left ⟶
        geometry.prior.cT.pt.left,
      IsPullback (geometry.pre.boundaries (@lastIndex.{u} K kField kClosed kZero G word i)).hom p
        (AppendChartStage.q d) δ₀ := ⟨pLast, hLast⟩
    exact hindex ▸ hpair
  choose lastMap hLast using h
  exact ⟨lastMap, hLast⟩


/-- Extend the prefix record on the cocone chosen by the append construction. -/
private theorem append_scalar_record
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (pre : @PrefixModel.{u} K kField kClosed kZero G word)
    (Q : Subalgebra ℤ K) (hRQ : pre.S ≤ Q) (hQ : Q.FG)
    (Result : ∀ (T : Subalgebra ℤ K) (_h : pre.S ≤ T) {Y : Scheme.{u}},
      (Y ⟶ Spec (.of T)) → (Y ⟶ pre.cG.pt.left) → Prop)
    (hmodels :
      let : Algebra pre.S Q := (Subalgebra.inclusion hRQ).toAlgebra
      appendStepModels (T := Q) pre.N pre.cG (bsdhToSpec G word) pre.m₀ (Result Q hRQ)) :
    ∃ out : @PrefixScalarModel.{u} K kField kClosed kZero G word pre,
      Result out.T out.hMT out.cT.pt.hom out.qT := by
  classical
  let : Algebra pre.S Q := (Subalgebra.inclusion hRQ).toAlgebra
  let : IsScalarTower pre.S Q K := Subalgebra.inclusion.isScalarTower_right hRQ K
  dsimp only at hmodels
  obtain ⟨ho, hd, cQ, qQ, mQ, ⟨hcQ⟩, hqQ, hmQ, hmComp, hmBase, hlegs,
    hsmoothModel, hsep, hraw⟩ := hmodels
  let NQ := @PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word pre Q hRQ
  have hsmooth : ∀ s, Algebra.Smooth Q (NQ.obj s) :=
    fixedFibreDiagram_smooth pre.N pre.smooth
  have hfp : ∀ s, Algebra.FinitePresentation Q (NQ.obj s) := by
    intro s
    let : Algebra.Smooth Q (NQ.obj s) := hsmooth s
    infer_instance
  let eQ := scalarDiagramComparison pre.S Q hRQ pre.N pre.F pre.e
  have heQ := scalarDiagramComparison_natural pre.S Q hRQ pre.N pre.F pre.e pre.he
  let vQ := modelEvaluation NQ pre.F eQ heQ
  let scalarMap := fixedScalarMap pre.S Q pre.N
  have hfactor := scalar_factor pre.S Q hRQ pre.N pre.F pre.e
  have hvalue : ∀ s x, (vQ.app s).hom ((scalarMap.app s).hom x) = (pre.v.app s).hom x := by
    intro s x
    exact (RingHom.congr_fun (hfactor s) x).trans (pre.eValue s x)
  have hcomp : ∀ s, (vQ.app s).hom.comp (scalarMap.app s).hom = (pre.v.app s).hom :=
    fun s => RingHom.ext (hvalue s)
  have hinjective : ∀ s, Function.Injective (vQ.app s).hom := by
    intro s
    let : Algebra.Smooth Q (NQ.obj s) := hsmooth s
    let : Module.Flat Q (NQ.obj s) := inferInstance
    exact (eQ s).injective.comp
      (Algebra.TensorProduct.includeRight_injective (R := Q) (A := K) (B := NQ.obj s)
        (show Function.Injective (algebraMap Q K) from Subtype.val_injective))
  have hproper : IsProper cQ.pt.hom := by
    let : IsProper pre.cG.pt.hom := pre.proper
    exact MorphismProperty.of_isPullback hqQ inferInstance
  have hnode : ∀ s, (pre.b.app (op s)).left ≫ mQ =
      Spec.map (CommRingCat.ofHom
        ((eQ s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cQ.ι.app (op s)).left := by
    intro s
    let φ := (eQ s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
    let φ₀ := (pre.e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
    have hsquare : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (scalarMap.app s) =
        Spec.map (CommRingCat.ofHom φ₀) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (hfactor s))
    have hbaseRing := evaluation_base (eQ s)
    have hbaseSpec := spec_square
      (CommRingCat.ofHom (algebraMap Q (NQ.obj s))) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (algebraMap Q K))
      (CommRingCat.ofHom (algebraMap K (pre.F.obj s)))
      (CommRingCat.hom_ext hbaseRing)
    have hbaseNode := node_base_square
      (pre.b.app (op s)).left mQ (Spec.map (CommRingCat.ofHom φ))
      (cQ.ι.app (op s)).left (bsdhToSpec G word) cQ.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Q K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (pre.F.obj s))))
      (Spec.map (CommRingCat.ofHom (algebraMap Q (NQ.obj s))))
      (pre.b.app (op s)).w hmBase (cQ.ι.app (op s)).w hbaseSpec
    exact chart_comparison
      (Spec.map (CommRingCat.ofHom (algebraMap pre.S Q))) pre.cG.pt.hom cQ.pt.hom qQ hqQ
      mQ pre.m₀ hmComp (pre.b.app (op s)).left
      (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom φ₀))
      (Spec.map (scalarMap.app s)) (cQ.ι.app (op s)).left (pre.cG.ι.app (op s)).left
      (pre.hbmodel s) (hlegs (op s)) hsquare hbaseNode
  let P : ∀ s, Polynomial (NQ.obj s) := fun s => Polynomial.map (scalarMap.app s).hom (pre.P s)
  have hdelta : ∀ s j hj k hk, (vQ.app s).hom
      (matchingScalarUnits pre.N NQ scalarMap pre.delta s j hj k hk : NQ.obj s) =
      (wordTransitionUnit G pre.F pre.beta s j hj k hk : pre.F.obj s) := by
    intro s j hj k hk
    exact (hvalue s (pre.delta s j hj k hk : pre.N.obj s)).trans (pre.hdelta s j hj k hk)
  have hco := matchingScalarUnits_cocycle pre.N NQ scalarMap pre.delta pre.hco
  have hn := matchingScalarUnits_natural pre.N NQ scalarMap pre.delta pre.hn
  have hmatch := matchingScalarPolynomial_leading pre.N NQ scalarMap pre.delta
    (fun j => pre.P (singletonIndex j)) pre.hr
  have hcoeffImage : ∀ j, (P (singletonIndex j)).coeff 2 =
      (scalarMap.app (singletonIndex j)).hom ((pre.P (singletonIndex j)).coeff 2) :=
    fun j => Polynomial.coeff_map (scalarMap.app (singletonIndex j)).hom 2
  have hcoeff : ∀ j, (vQ.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G pre.F pre.point pre.a j := by
    intro j
    exact (congrArg (vQ.app (singletonIndex j)).hom (hcoeffImage j)).trans
      ((hvalue (singletonIndex j) ((pre.P (singletonIndex j)).coeff 2)).trans (pre.hCoefficient j))
  let boundaries : Fin word.length → Over cQ.pt.left := fun k =>
    Over.mk (pullback.fst qQ (pre.boundaries k).hom)
  let qB := fun k : Fin word.length => pullback.snd qQ (pre.boundaries k).hom
  have hclosed : ∀ k, IsClosedImmersion (boundaries k).hom := by
    intro k
    let : IsClosedImmersion (pre.boundaries k).hom := pre.hclosed k
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback qQ (pre.boundaries k).hom).flip
      inferInstance
  let wB := fun k : Fin word.length =>
    (Category.assoc (bsdhOmitMap G word k) mQ qQ).trans
      ((congrArg (fun z => bsdhOmitMap G word k ≫ z) hmComp).trans (pre.hnB k).w)
  let nB := fun k : Fin word.length =>
    pullback.lift (bsdhOmitMap G word k ≫ mQ) (pre.nB k) (wB k)
  have hnB : ∀ k, IsPullback (bsdhOmitMap G word k) (nB k) mQ (boundaries k).hom := by
    intro k
    exact boundary_square (bsdhOmitMap G word k) (pre.nB k) pre.m₀
      (pre.boundaries k).hom (pre.hnB k) qQ mQ hmComp (nB k)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  let out : @PrefixScalarModel.{u} K kField kClosed kZero G word pre := {
    T := Q
    hMT := hRQ
    hT := hQ
    cT := cQ
    hcT := hcQ
    qT := qQ
    hqT := hqQ
    mT := mQ
    hmT := hmQ
    hmTComp := hmComp
    hLeg := fun s => hlegs (op s)
    nOpen := fun {s t} f => ho f.op
    nDir := hd
    fp := hfp
    smooth := hsmooth
    proper := hproper
    smoothModel := hsmoothModel
    he := heQ
    v := vQ
    hv := hinjective
    eValue := fun _ _ => rfl
    hbmodel := hnode
    hdelta := hdelta
    hco := hco
    hn := hn
    P := P
    hP := fun s => Polynomial.natDegree_map_le.trans (pre.hP s)
    hr := hmatch
    hCoefficientImage := hcoeffImage
    hCoefficient := hcoeff
    boundaries := boundaries
    hclosed := hclosed
    qB := qB
    hqB := fun k => IsPullback.of_hasPullback qQ (pre.boundaries k).hom
    nB := nB
    hnB := hnB }
  exact ⟨out, hraw⟩



end RetainedCharacter

private theorem omitted_atlas_section {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word)
    {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    (L : @NextLetter.{u} K kField kClosed kZero G word M i)
    (D : {s : Finset M.J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (M.N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (δ : M.cG.pt.left ⟶ cD.pt)
    (hδ : ∀ s, (M.cG.ι.app (op s)).left ≫ δ =
      projectiveLineSection (M.N.obj s) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        (eP s).inv ≫ cD.ι.app (op s))
    (m : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ cD.pt)
    (hchart : ∀ s, projectiveAppendChart G i (M.F.obj s)
      ((algSpec (.of K)).map (M.F.map
        (singletonArrow s (M.sel s).val (M.sel s).property)).op)
      (L.c (M.sel s).val) ≫ m =
      projectiveCoeffMap (ULift.{u} (Fin 2))
        ((M.e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
          (eP s).inv ≫ cD.ι.app (op s)) :
    ∃ d : bsdhScheme G word ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))),
      d ≫ bsdhAppendFst G word i = 𝟙 _ ∧
      d ≫ bsdhMap G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) = bsdhMap G word ∧
      d ≫ m = M.m₀ ≫ δ := by
  have hb : IsColimit (Cocone.mk (bsdhScheme G word)
      (Functor.whiskerRight M.b (Over.forget (Spec (.of K))))) :=
    @isColimitOfPreserves
      (Over (Spec (.of K))) (inferInstanceAs (Category.{u} (Over (Spec (.of K)))))
      Scheme.{u} (inferInstanceAs (Category.{u} Scheme.{u}))
      {s : Finset M.J // s.Nonempty}ᵒᵖ
      (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}ᵒᵖ))
      (M.F.op ⋙ algSpec (.of K)) (Over.forget (Spec (.of K)))
      (Cocone.mk (Over.mk (bsdhToSpec G word)) M.b) M.hb
      (inferInstanceAs (PreservesColimit (M.F.op ⋙ algSpec (.of K))
        (Over.forget (Spec (.of K)))))
  have hp : ∀ s j hj,
      ((algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op).left ≫
        (M.b.app (op (singletonIndex j))).left = (M.b.app (op s)).left := by
    intro s j hj
    exact congrArg (fun f => f.left)
      ((M.b.naturality (singletonArrow s j hj).op).trans (Category.comp_id _))
  have ha : ∀ j, (M.a j).left ≫ flagSchemeChart G (M.point j) =
      (M.b.app (op (singletonIndex j))).left ≫ bsdhMap G word := M.ha
  obtain ⟨d, _, hdπ, hdτ⟩ := @bsdh_omitted_section.{u} K kField kClosed kZero G word i
  have hdm := @bundle_infinity_comparison.{u} K M.S kField kClosed kZero
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
      (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) M.S)
    G word i M.J
    (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j))))
    (fun j => M.b.app (op (singletonIndex j))) M.F M.N M.e M.sel
    (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op)
    M.point M.a L.c ha L.hend (Functor.whiskerRight M.b (Over.forget (Spec (.of K))))
    hb hp (fun s => (L.hcart s).w.symm)
    M.cG D eP cD δ hδ M.m₀ m M.hbmodel hchart d hdπ hdτ
  exact ⟨d, hdπ, hdτ, hdm⟩

section Atlas

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (R : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List (@simpleRootIndex.{u} K kField kClosed kZero G)) (i : (@simpleRootIndex.{u} K kField kClosed kZero G))
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)


variable
    (g : J → G.points)
    (aGeom : ∀ j, V₀ j ⟶
      (oppositeUnipotentVariety G).toOver)
    (hend : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (aGeom j ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (g j))
    (_hbbase : ∀ s, b.app (op s) ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))

private theorem expose_left {P Q : Prop} {Z : P → Prop}
    (h : P ∧ Q) (f : ∀ hp, Q → Z hp) : ∃ hp, Z hp :=
  ⟨h.1, f h.1 h.2⟩

private def atlasRetentionResult : Prop :=
  letI := @wordSchemeSeparated.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
  let scale := fun s j hj k hk ↦
    Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  ∃ (c₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), N.obj s),
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] (c₀ s j hj k hk : N.obj s)) =
      (scale s j hj k hk : F.obj s)) ∧
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] a₀ s j hj k hk) = shift s j hj k hk) ∧
    (∀ s j hj k hk l hl, c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk ∧
      a₀ s j hj l hl = (c₀ s k hk l hl : N.obj s) * a₀ s j hj k hk + a₀ s k hk l hl) ∧
    (∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c₀ s j hj k hk) =
        c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a₀ s j hj k hk) = a₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
    ∃ (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
      (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
      (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))),
      (∀ s, π.app (op s) = (eP s).hom ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2))) ∧
      (∀ s t (f : s ⟶ t), D.map f.op ≫ (eP s).hom = (eP t).hom ≫
        (projectiveLineScalingIso
          (c₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        (projectiveLineTranslationIso
          (a₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom) ∧
      π.Equifibered ∧ ∃ (cD : Cocone D) (q : cD.pt ⟶ cG.pt.left),
        Nonempty (IsColimit cD) ∧
        (∀ s, cD.ι.app s ≫ q = π.app s ≫ (cG.ι.app s).left) ∧
        (∀ s, IsPullback (π.app s) (cD.ι.app s) (cG.ι.app s).left q) ∧
        IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
        ∃ (hOpen : ∀ s, IsOpenImmersion (cD.ι.app s))
          (hCover : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
            ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
              (pullback.fst f (cD.ι.app s)) z = y),
        ∃ m : bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) ⟶ cD.pt,
          ∃ hmCart : IsPullback m (bsdhToSpec G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))) (q ≫ cG.pt.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap R K))),
          IsPullback m (bsdhAppendFst G word i) q m₀ ∧
          (∀ s, projectiveAppendChart G i (F.obj s)
              (p s (sel s).val (sel s).property) (c (sel s).val) ≫ m =
            projectiveCoeffMap (ULift.{u} (Fin 2))
              ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
                (eP s).inv ≫ cD.ι.app (op s)) ∧
          ∃ hPolynomial : ∀ s (j : ULift.{u} (Fin 2)),
            (projectiveLinePolynomialChart (F.obj s) j ≫
                projectiveAppendChart G i (F.obj s)
                  (p s (sel s).val (sel s).property) (c (sel s).val)) ≫ m =
              Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
                ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) ≫
                (projectiveLinePolynomialChart (N.obj s) j ≫
                  (eP s).inv ≫ cD.ι.app (op s)) ∧
            (projectiveLinePolynomialChart (N.obj s) j ≫
                (eP s).inv ≫ cD.ι.app (op s)) ≫ q =
              Spec.map (CommRingCat.ofHom (Polynomial.C : N.obj s →+* Polynomial (N.obj s))) ≫
                (cG.ι.app (op s)).left ∧
            (projectiveLinePolynomialChart (F.obj s) j ≫
                projectiveAppendChart G i (F.obj s)
                  (p s (sel s).val (sel s).property) (c (sel s).val)) ≫
                  bsdhAppendFst G word i =
              Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫
                b.app (op s),
          ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T),
            let input : @AppendChartData.{u} K kField kClosed kZero R G word i :=
              @AppendChartData.mk.{u} K kField kClosed kZero R G word i
                J F N e sel V₀ p c g aGeom hend (fun s => b.app (op s)) _hbbase
            let old : @AppendChartContext.{u} K kField kClosed kZero R G word i input :=
              @AppendChartContext.mk.{u} K kField kClosed kZero R G word i input
                D eP cD hOpen hCover (q ≫ cG.pt.hom) m hmCart
                (fun s j => (hPolynomial s j).1)
                (fun s j => (hPolynomial s j).2.2)
            ∃ δ₀ : cG.pt.left ⟶ cD.pt,
              IsClosedImmersion δ₀ ∧ δ₀ ≫ q = 𝟙 cG.pt.left ∧
              (∀ s, projectiveLineSection (N.obj s) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
                (eP s).inv ≫ cD.ι.app (op s) = (cG.ι.app (op s)).left ≫ δ₀) ∧
              ∃ dNative : bsdhScheme G word ⟶ bsdhScheme G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))),
                dNative ≫ bsdhAppendFst G word i = 𝟙 _ ∧
                dNative ≫ bsdhMap G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G)))) = bsdhMap G word ∧
                dNative ≫ m = m₀ ≫ δ₀ ∧
                @wordStageRetention.{u} K kField kClosed kZero G word i R input old T hRT



private theorem retain_append_atlas {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word)
    {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    (L : @NextLetter.{u} K kField kClosed kZero G word M i)
    (h : @matchingAppendAtlas.{u} K kField kClosed kZero M.S G word i M.J
      (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F M.N M.e
      (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op)
      L.c M.beta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) M.cG M.m₀) :
    @atlasRetentionResult.{u} K kField kClosed kZero M.S G word i M.J
      (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F M.N M.e
      (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op)
      L.c M.beta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) M.cG M.m₀
      M.point M.a L.hend (fun s => (M.b.app (op s)).w) := by
  let := @wordSchemeSeparated.{u} K kField kClosed kZero G (@List.append.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) word (@List.cons.{u} (@simpleRootIndex.{u} K kField kClosed kZero G) i (@List.nil.{u} (@simpleRootIndex.{u} K kField kClosed kZero G))))
  apply map_exists_witness h
  intro c₀ h
  apply map_exists_witness h
  intro a₀' h
  apply map_and_tail h
  intro hc₀ h
  apply map_and_tail h
  intro ha₀ h
  apply map_and_tail h
  intro hco h
  apply map_and_tail h
  intro hn h
  apply map_exists_witness h
  intro D h
  apply map_exists_witness h
  intro eP h
  apply map_exists_witness h
  intro π h
  apply map_and_tail h
  intro hπ h
  apply map_and_tail h
  intro hD h
  apply map_and_tail h
  intro hπcart h
  apply map_exists_witness h
  intro cD h
  apply map_exists_witness h
  intro q h
  apply map_and_tail h
  intro hcD h
  apply map_and_tail h
  intro hqlegs h
  apply map_and_tail h
  intro hqcart h
  apply map_and_tail h
  intro hproper h
  apply map_and_tail h
  intro hsmooth h
  apply map_and_tail h
  intro hconnected h
  apply map_exists_witness h
  intro hOpen h
  apply map_exists_witness h
  intro hCover h
  apply map_exists_witness h
  intro m h
  apply expose_left h
  intro hmCart h
  apply map_and_tail h
  intro hmAppend h
  apply map_and_tail h
  intro hProjective h
  apply expose_left h
  intro hPolynomial h
  apply map_exists_witness h
  intro T h
  apply map_exists_witness h
  intro hRT h
  let input : @AppendChartData.{u} K kField kClosed kZero M.S G word i :=
    @AppendChartData.mk.{u} K kField kClosed kZero M.S G word i
      M.J M.F M.N M.e M.sel (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) L.c M.point M.a L.hend (fun s => (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))).app (op s)) (fun s => (M.b.app (op s)).w)
  let old : @AppendChartContext.{u} K kField kClosed kZero M.S G word i input :=
    @AppendChartContext.mk.{u} K kField kClosed kZero M.S G word i input
      D eP cD hOpen hCover (q ≫ M.cG.pt.hom) m hmCart
                (fun s j => (hPolynomial s j).1)
                (fun s j => (hPolynomial s j).2.2)
  obtain ⟨δ₀, hδSection, hδClosed, hδNode⟩ :=
    @projective_bundle_infinity.{u} {s : Finset M.J // s.Nonempty} M.S (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N D π (fun s => eP s.unop) (fun s => hπ s.unop)
      (fun {s t} f => c₀ s.unop (M.sel s.unop).val (M.sel s.unop).property
        (M.sel t.unop).val ((leOfHom f.unop) (M.sel t.unop).property))
      (fun {s t} f => a₀' s.unop (M.sel s.unop).val (M.sel s.unop).property
        (M.sel t.unop).val ((leOfHom f.unop) (M.sel t.unop).property))
      (fun {s t} f => hD t.unop s.unop f.unop)
      M.cG M.hcG cD q (@IsProper.toIsSeparated.{u} cD.pt M.cG.pt.left q hproper) hqlegs
  obtain ⟨dNative, hdπ, hdτ, hδNative⟩ :=
    @omitted_atlas_section.{u} K kField kClosed kZero G word M i L
      D eP cD δ₀ (fun s => hδNode (op s)) m hProjective
  refine ⟨δ₀, hδClosed, hδSection, (fun s => (hδNode (op s)).symm),
    dNative, hdπ, hdτ, hδNative, ?_⟩
  exact @retain_word_scalar_stage.{u} K kField kClosed kZero G word i M.S input old T hRT h


end Atlas

private theorem retain_append_application {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word) {i : (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (L : @NextLetter.{u} K kField kClosed kZero G word M i)
    (coefficients : @PrefixScalarModel.{u} K kField kClosed kZero G word M)
    (hRoot : @wordPolynomialData.{u} K kField kClosed kZero G M.J M.F M.point M.a i coefficients.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.T) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word M coefficients.T coefficients.hMT) coefficients.v coefficients.P)
    (T : Subalgebra ℤ K) (hCT : coefficients.prefix.S ≤ T) (hT : T.FG)
    (hCoefficients : (let scalarAlgebra : Algebra coefficients.prefix.S T := (Subalgebra.inclusion hCT).toAlgebra
       let scalarTower : IsScalarTower coefficients.prefix.S T K := Subalgebra.inclusion.isScalarTower_right hCT K
       @appendCoefficientSpec.{u} coefficients.prefix.S T K M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
         (@Field.toCommRing K kField) scalarAlgebra (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) T)
         (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) coefficients.prefix.S) scalarTower coefficients.prefix.N M.F coefficients.prefix.e
         coefficients.prefix.delta (fun j => coefficients.prefix.P (singletonIndex j))))
    (h : @appendMatchingApplicationSpec.{u} K kField kClosed kZero coefficients.prefix.S
      G word i M.J (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F coefficients.prefix.N coefficients.prefix.e
      (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) L.c M.beta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) coefficients.cT coefficients.mT T hCT) :
    ∃ prior : @PrefixScalarModel.{u} K kField kClosed kZero G word coefficients.prefix,
      @wordPolynomialData.{u} K kField kClosed kZero G M.J M.F M.point M.a i prior.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) prior.T) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T prior.hMT) prior.v prior.P ∧ (let scalarAlgebra : Algebra coefficients.prefix.S prior.T := (Subalgebra.inclusion prior.hMT).toAlgebra
       let scalarTower : IsScalarTower coefficients.prefix.S prior.T K := Subalgebra.inclusion.isScalarTower_right prior.hMT K
       @appendCoefficientSpec.{u} coefficients.prefix.S prior.T K M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) prior.T)
         (@Field.toCommRing K kField) scalarAlgebra (inferInstanceAs (Algebra prior.T K))
         (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) coefficients.prefix.S) scalarTower coefficients.prefix.N M.F coefficients.prefix.e
         coefficients.prefix.delta (fun j => coefficients.prefix.P (singletonIndex j))) ∧ @atlasRetentionResult.{u} K kField kClosed kZero prior.T G word i M.J (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T prior.hMT) prior.prefix.e (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) L.c M.beta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) prior.cT prior.mT M.point M.a L.hend (fun s => (M.b.app (op s)).w) := by
  let scalarAlgebra : Algebra coefficients.prefix.S T := (Subalgebra.inclusion hCT).toAlgebra
  let scalarTower : IsScalarTower coefficients.prefix.S T K :=
    Subalgebra.inclusion.isScalarTower_right hCT K
  obtain ⟨hopen, hdir, he, cT, qT, ⟨hcT⟩, hqT, hlegs, mT, hmT,
    hmComp, hmlegs, hAtlas⟩ := h
  let v := @modelEvaluation.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) T K (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    (@Field.toCommRing K kField) (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) T) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT) M.F (@scalarDiagramComparison.{u,u,u} K kField coefficients.prefix.S T hCT {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.N M.F coefficients.prefix.e) he
  have hvalue : ∀ s x, (v.app s).hom (((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app s).hom x) =
      (coefficients.prefix.v.app s).hom x := by
    intro s x
    change (@scalarDiagramComparison.{u,u,u} K kField coefficients.prefix.S T hCT {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.N M.F coefficients.prefix.e) s ((1 : K) ⊗ₜ[T] ((1 : T) ⊗ₜ[coefficients.prefix.S] x)) = _
    rw [@scalarDiagramComparison_tmul.{u,u,u} K kField coefficients.prefix.S T hCT
      {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.N M.F coefficients.prefix.e s 1 1 x]
    exact (congrArg (fun k : K => coefficients.prefix.e s (k ⊗ₜ[coefficients.prefix.S] x))
      (show algebraMap T K (1 : T) * (1 : K) = 1 by simp only [map_one, one_mul])).trans
        (coefficients.prefix.eValue s x)
  have hcomp : ∀ s, (v.app s).hom.comp ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app s).hom =
      (coefficients.prefix.v.app s).hom := by
    intro s
    exact RingHom.ext (hvalue s)
  let P : ∀ s, Polynomial ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) :=
    fun s => Polynomial.map ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app s).hom (coefficients.prefix.P s)
  have hP := @map_quadratic_relations.{u,u} {s : Finset M.J // s.Nonempty}
    (fun s => coefficients.prefix.N.obj s) (fun s => (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) (fun s => M.F.obj s)
    (fun s => inferInstanceAs (CommRing (coefficients.prefix.N.obj s)))
    (fun s => inferInstanceAs (CommRing ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s)))
    (fun s => inferInstanceAs (CommRing (M.F.obj s)))
    (fun s => ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app s).hom)
    (fun s => (coefficients.prefix.v.app s).hom) (fun s => (v.app s).hom) hcomp
    coefficients.prefix.P
    (fun s => Polynomial.map (Spec.preimage
      ((@selectedFrame.{u} K kField kClosed kZero G M.J M.F M.a s) ≫
        flagChartMap G (M.point (@selectedIndex.{u} M.J s))).left).hom
      (DeterminantSection.simpleFramePolynomial G i (DeterminantSection.positiveDetCoefficient G)))
    (fun s => (Spec.preimage
      ((@selectedFrame.{u} K kField kClosed kZero G M.J M.F M.a s) ≫
        flagChartMap G (M.point (@selectedIndex.{u} M.J s))).left).hom
      (DeterminantSection.positiveDetCoefficient G)) (fun s => hRoot s)
  have hfp : ∀ s, Algebra.FinitePresentation T ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) := by
    intro s
    let : Algebra.FinitePresentation coefficients.prefix.S (coefficients.prefix.N.obj s) :=
      coefficients.prefix.fp s
    change Algebra.FinitePresentation T (T ⊗[coefficients.prefix.S] coefficients.prefix.N.obj s)
    infer_instance
  have hsmooth : ∀ s, Algebra.Smooth T ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) := by
    intro s
    let : Algebra.Smooth coefficients.prefix.S (coefficients.prefix.N.obj s) :=
      coefficients.prefix.smooth s
    change Algebra.Smooth T (T ⊗[coefficients.prefix.S] coefficients.prefix.N.obj s)
    infer_instance
  have hinjective : ∀ s, Function.Injective (v.app s).hom := by
    intro s
    let : Algebra.Smooth T ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) := hsmooth s
    let : Module.Flat T ((@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) := inferInstance
    change Function.Injective (fun x => (@scalarDiagramComparison.{u,u,u} K kField coefficients.prefix.S T hCT {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.N M.F coefficients.prefix.e) s ((1 : K) ⊗ₜ[T] x))
    exact ((@scalarDiagramComparison.{u,u,u} K kField coefficients.prefix.S T hCT {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.N M.F coefficients.prefix.e) s).injective.comp
      (Algebra.TensorProduct.includeRight_injective (R := T) (A := K)
        (B := (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s)
        (show Function.Injective (algebraMap T K) from Subtype.val_injective))
  have hdelta : ∀ s j hj k hk, (v.app s).hom
      ((@matchingScalarUnits.{u} coefficients.prefix.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
        coefficients.prefix.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N) coefficients.prefix.delta) s j hj k hk :
        (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT).obj s) =
      (@wordTransitionUnit.{u} K kField kClosed kZero G M.J M.F M.beta s j hj k hk : M.F.obj s) := by
    intro s j hj k hk
    exact (hvalue s (coefficients.prefix.delta s j hj k hk : coefficients.prefix.N.obj s)).trans
      (coefficients.prefix.hdelta s j hj k hk)
  have hco := @matchingScalarUnits_cocycle.{u} coefficients.prefix.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    coefficients.prefix.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N) coefficients.prefix.delta coefficients.prefix.hco
  have hn := @matchingScalarUnits_natural.{u} coefficients.prefix.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    coefficients.prefix.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N) coefficients.prefix.delta coefficients.prefix.hn
  have hmatch := @matchingScalarPolynomial_leading.{u} coefficients.prefix.S T M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T)
    coefficients.prefix.N (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix T hCT) (@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N) coefficients.prefix.delta
    (fun j => coefficients.prefix.P (singletonIndex j)) coefficients.prefix.hr
  have htop : ∀ j, (P (singletonIndex j)).coeff 2 =
      ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app (singletonIndex j)).hom ((coefficients.prefix.P (singletonIndex j)).coeff 2) :=
    fun j => Polynomial.coeff_map ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) coefficients.prefix.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) T) scalarAlgebra coefficients.prefix.N).app (singletonIndex j)).hom 2
  have hsingle : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      @wordRingCoefficient.{u} K kField kClosed kZero G M.J M.F M.point M.a j := by
    intro j
    exact (congrArg (v.app (singletonIndex j)).hom (htop j)).trans
      ((hvalue (singletonIndex j) ((coefficients.prefix.P (singletonIndex j)).coeff 2)).trans
        (coefficients.prefix.hCoefficient j))
  let boundaries : Fin word.length → Over cT.pt.left :=
    fun k => Over.mk (pullback.fst qT (coefficients.prefix.boundaries k).hom)
  let nB : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶ (boundaries k).left :=
    fun k => pullback.lift ((@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ mT)
      (coefficients.prefix.nB k) (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun z => (@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ z)
            hmComp).trans (coefficients.prefix.hnB k).w))
  have hboundary : ∀ k, IsPullback
      (@bsdhOmitMap.{u} K kField kClosed kZero G word k) (nB k) mT (boundaries k).hom := by
    intro k
    have hf : nB k ≫ pullback.fst qT (coefficients.prefix.boundaries k).hom =
        (@bsdhOmitMap.{u} K kField kClosed kZero G word k) ≫ mT := pullback.lift_fst _ _ _
    have hs : nB k ≫ pullback.snd qT (coefficients.prefix.boundaries k).hom =
        coefficients.prefix.nB k := pullback.lift_snd _ _ _
    have houter : IsPullback (@bsdhOmitMap.{u} K kField kClosed kZero G word k)
        (nB k ≫ pullback.snd qT (coefficients.prefix.boundaries k).hom) (mT ≫ qT)
        (coefficients.prefix.boundaries k).hom := by
      erw [hs, hmComp]
      exact coefficients.prefix.hnB k
    exact houter.of_bot hf.symm (IsPullback.of_hasPullback qT (coefficients.prefix.boundaries k).hom)
  let prior : @PrefixScalarModel.{u} K kField kClosed kZero G word coefficients.prefix :=
    { T := T
      hMT := hCT
      hT := hT
      cT := cT
      hcT := hcT
      qT := qT
      hqT := hqT
      mT := mT
      hmT := hmT
      hmTComp := hmComp
      hLeg := hlegs
      nOpen := hopen
      nDir := hdir
      fp := hfp
      smooth := hsmooth
      proper := MorphismProperty.of_isPullback hqT coefficients.prefix.proper
      smoothModel := MorphismProperty.of_isPullback hqT coefficients.prefix.smoothModel
      he := he
      v := v
      hv := hinjective
      eValue := fun _ _ => rfl
      hbmodel := hmlegs
      hdelta := hdelta
      hco := hco
      hn := hn
      P := P
      hP := fun s => (hP s).1
      hr := hmatch
      hCoefficientImage := htop
      hCoefficient := hsingle
      boundaries := boundaries
      hclosed := fun k => MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback qT (coefficients.prefix.boundaries k).hom).flip
        (coefficients.prefix.hclosed k)
      qB := fun k => pullback.snd qT (coefficients.prefix.boundaries k).hom
      hqB := fun k => IsPullback.of_hasPullback qT (coefficients.prefix.boundaries k).hom
      nB := nB
      hnB := hboundary }
  refine ⟨prior, hP, hCoefficients, ?_⟩
  let next : @NextLetter.{u} K kField kClosed kZero G word prior.prefix i :=
    { c := L.c, hchart := L.hchart, hcart := L.hcart, hend := L.hend }
  exact @retain_append_atlas.{u} K kField kClosed kZero G word prior.prefix i next hAtlas


/-- The carried prefix and next-letter charts produce coefficient and prior
models with the root polynomials and projective append data retained. -/
private theorem retain_append_models {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : @PrefixModel.{u} K kField kClosed kZero G word) (i : (@simpleRootIndex.{u} K kField kClosed kZero G))
    (L : @NextLetter.{u} K kField kClosed kZero G word M i) :
    ∃ coefficients : @PrefixScalarModel.{u} K kField kClosed kZero G word M,
      ∃ prior : @PrefixScalarModel.{u} K kField kClosed kZero G word coefficients.prefix,
        @wordPolynomialData.{u} K kField kClosed kZero G M.J M.F M.point M.a i prior.T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) prior.T) (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T prior.hMT) prior.v prior.P ∧ (let scalarAlgebra : Algebra coefficients.prefix.S prior.T := (Subalgebra.inclusion prior.hMT).toAlgebra
       let scalarTower : IsScalarTower coefficients.prefix.S prior.T K := Subalgebra.inclusion.isScalarTower_right prior.hMT K
       @appendCoefficientSpec.{u} coefficients.prefix.S prior.T K M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) coefficients.prefix.S) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) prior.T)
         (@Field.toCommRing K kField) scalarAlgebra (inferInstanceAs (Algebra prior.T K))
         (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) coefficients.prefix.S) scalarTower coefficients.prefix.N M.F coefficients.prefix.e
         coefficients.prefix.delta (fun j => coefficients.prefix.P (singletonIndex j))) ∧ @atlasRetentionResult.{u} K kField kClosed kZero prior.T G word i M.J (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F (@PrefixModel.scalarDiagram.{u} K kField kClosed kZero G word coefficients.prefix prior.T prior.hMT) prior.prefix.e (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) L.c M.beta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) prior.cT prior.mT M.point M.a L.hend (fun s => (M.b.app (op s)).w) := by
  obtain ⟨coefficients, hRoot⟩ := @retain_prefix_polynomials.{u} K kField kClosed kZero G word M i
  have hb : IsColimit (Cocone.mk (bsdhScheme G word) (Functor.whiskerRight M.b (Over.forget (Spec (.of K))))) :=
    @isColimitOfPreserves
      (Over (Spec (.of K))) (inferInstanceAs (Category.{u} (Over (Spec (.of K)))))
      Scheme.{u} (inferInstanceAs (Category.{u} Scheme.{u}))
      {s : Finset M.J // s.Nonempty}ᵒᵖ
      (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}ᵒᵖ))
      (M.F.op ⋙ algSpec (.of K)) (Over.forget (Spec (.of K)))
      (Cocone.mk (Over.mk (bsdhToSpec G word)) M.b) M.hb
      (inferInstanceAs (PreservesColimit (M.F.op ⋙ algSpec (.of K))
        (Over.forget (Spec (.of K)))))
  have hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (M.F.map f).op ≫
        (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op =
      (algSpec (.of K)).map (M.F.map (singletonArrow t j ((leOfHom f) hj))).op := by
    intro s t f j hj
    exact ((M.F.op ⋙ algSpec (.of K)).map_comp f.op (singletonArrow s j hj).op).symm.trans
      (congrArg (fun g : op t ⟶ op (singletonIndex j) =>
        (M.F.op ⋙ algSpec (.of K)).map g) (Subsingleton.elim _ _))
  have result := @exists_append_matching_application.{u} K kField kClosed kZero
    coefficients.prefix.S coefficients.prefix.hS G word i M.J (fun j => (algSpec (.of K)).obj (op (M.F.obj (singletonIndex j)))) M.F coefficients.prefix.N
    coefficients.prefix.e coefficients.prefix.he M.fOpen M.fDir
    coefficients.prefix.nOpen coefficients.prefix.nDir (fun s j hj => (algSpec (.of K)).map (M.F.map (singletonArrow s j hj)).op) L.c hpn M.beta L.hchart M.hnatural
    M.hbeta M.sel (Functor.whiskerRight M.b (Over.forget (Spec (.of K)))) hb (fun s => (M.b.app (op s)).w) L.hcart coefficients.cT coefficients.mT
    coefficients.hmT coefficients.hbmodel M.finite coefficients.prefix.fp coefficients.prefix.smooth
    coefficients.proper coefficients.smoothModel coefficients.prefix.delta coefficients.prefix.hco
    coefficients.prefix.hn (fun j => coefficients.prefix.P (singletonIndex j))
    (fun j => coefficients.prefix.hP (singletonIndex j)) coefficients.prefix.hr coefficients.hcT
  obtain ⟨T, hCT, hT, hGeometry, hCoefficients⟩ := result
  obtain ⟨prior, hPriorRoot, hPriorCoefficients, hAtlas⟩ := @retain_append_application.{u} K kField kClosed kZero
    G word M i L coefficients hRoot T hCT hT hCoefficients hGeometry
  exact ⟨coefficients, prior, hPriorRoot, hPriorCoefficients, hAtlas⟩





end SchubertGeometry
