import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageSections
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageGeometry
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarModelComparisons
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframes on coefficient extensions

A polynomial open chart and a word endpoint determine one chart preimage.
Its section coordinates are retained in coframes over a coefficient extension.
-/

set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct
namespace SchubertGeometry.RetainedCharacter
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private FrobeniusSplitting.modelComparison FrobeniusSplitting.modelComparison_projection from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private FrobeniusSplitting.scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private DeterminantSection.cartesianLift DeterminantSection.cartesianLift_projection
  DeterminantSection.cartesian_map DeterminantSection.naturality_square
  DeterminantSection.intermediate_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOpenStages
open private DeterminantSection.composite_projection from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChartModels

private theorem separated_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsSeparated f) (hY : Y.IsSeparated) : X.IsSeparated := by
  let : IsSeparated f := hf
  let : Y.IsSeparated := hY
  constructor
  rw [← Limits.terminal.comp_from f]
  infer_instance

private def stageProjection {K : Type u} [kComm : CommRing K]
    (S : Subalgebra ℤ K) {Y : Scheme.{u}} (a : Y ⟶ Spec (.of S))
    (t : @CoefficientStage.{u} K kComm S) :
    (@stageScalarModel.{u} K kComm S Y a t).left ⟶ Y :=
  Limits.pullback.snd (Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion t.property.2).toRingHom)) a

private structure CoframeCertificate
    {K : Type u} [kComm : CommRing K] (R : Subalgebra ℤ K)
    (D : Type u) [dComm : CommRing D] (Y : Over (Spec (.of R))) (Z : Scheme.{u})
    (j : Y.left ⟶ Z) (b : Y.left ⟶ Spec (.of (Polynomial D)))
    (L : ℕ → Z.Modules) (s : ∀ n, SheafOfModules.unit Z.ringCatSheaf ⟶ L n)
    (w : Dˣ) where
  stage : @CoefficientStage.{u} K kComm R
  frames : ∀ n : ℕ,
    ∃ E : (pullback (@stageProjection.{u} K kComm R Y.left Y.hom stage)).obj
        ((pullback j).obj (L n)) ≅
        SheafOfModules.unit (@stageScalarModel.{u} K kComm R Y.left Y.hom stage).left.ringCatSheaf,
      @pullSection.{u} (@stageScalarModel.{u} K kComm R Y.left Y.hom stage).left Y.left
          (@stageProjection.{u} K kComm R Y.left Y.hom stage) ((pullback j).obj (L n))
          (@pullSection.{u} Y.left Z j (L n) (s n)) ≫ E.hom =
        globalSectionsSmul
          (SheafOfModules.unit (@stageScalarModel.{u} K kComm R Y.left Y.hom
            stage).left.ringCatSheaf)
          (((@stageProjection.{u} K kComm R Y.left Y.hom stage) ≫ b).appTop.hom
            ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom
              ((Polynomial.C (w : D) * (Polynomial.X : Polynomial D) ^ 2) ^ n)))

private structure CoframeStage
    {K : Type u} [kComm : CommRing K] (S : Subalgebra ℤ K)
    (stage0 : @CoefficientStage.{u} K kComm S)
    (B : Type u) [bComm : CommRing B] [sB : Algebra stage0.val B]
    (A : Type u) [aComm : CommRing A] [kA : Algebra K A]
    (coefficientIso : K ⊗[stage0.val] B ≃ₐ[K] A)
    (C F : Over (Spec (.of S))) (FK : Over (Spec (.of K)))
    (qF0 : FK.left ⟶ (@stageScalarModel.{u} K kComm S F.left F.hom stage0).left)
    (fK : (@polynomialModel.{u} K A kComm aComm kA).left ⟶ FK.left)
    (Z : Scheme.{u}) (qOriginal : C.left ⟶ Z) (endpoint : C ⟶ F)
    (L : ℕ → Z.Modules) (sections : ∀ n, SheafOfModules.unit Z.ringCatSheaf ⟶ L n) where
  stage : @CoefficientStage.{u} K kComm stage0.val
  chart : @PolynomialOpenModel.{u} stage0.val stage.val K B A
      (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
      kComm bComm aComm (Subalgebra.inclusion stage.property.2).toAlgebra
      (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
      sB kA (Subalgebra.inclusion.isScalarTower_right stage.property.2 K) coefficientIso
      (@stageScalarModel.{u} K kComm S F.left F.hom stage0) FK qF0 fK
  arrow : (@stageScalarModel.{u} K kComm S C.left C.hom (@singleScalarStage.{u} K kComm S stage0
    stage)) ⟶ (@PolynomialOpenModel.flagModel.{u} stage0.val stage.val K B A
      (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
      kComm bComm aComm (Subalgebra.inclusion stage.property.2).toAlgebra
      (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
      sB kA (Subalgebra.inclusion.isScalarTower_right stage.property.2 K) coefficientIso
      (@stageScalarModel.{u} K kComm S F.left F.hom stage0) FK qF0 fK chart)
  arrow_projection : arrow.left ≫ ((@PolynomialOpenModel.projection.{u} stage0.val stage.val K B A
      (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
      kComm bComm aComm (Subalgebra.inclusion stage.property.2).toAlgebra
      (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
      sB kA (Subalgebra.inclusion.isScalarTower_right stage.property.2 K) coefficientIso
      (@stageScalarModel.{u} K kComm S F.left F.hom stage0) FK qF0 fK chart) ≫
      (@stageProjection.{u} K kComm S F.left F.hom stage0)) =
    (@stageProjection.{u} K kComm S C.left C.hom (@singleScalarStage.{u} K kComm S stage0 stage)) ≫
      endpoint.left
  nontrivial : ∀ (κ : Type u) [Field κ] [Algebra stage0.val κ], Nontrivial (κ ⊗[stage0.val] B)
  unit : letI : Algebra stage0.val stage.val := (Subalgebra.inclusion stage.property.2).toAlgebra
    (stage.val ⊗[stage0.val] B)ˣ
  coframe :
    letI : Algebra stage0.val stage.val := (Subalgebra.inclusion stage.property.2).toAlgebra
    let a := Arrow.mk (@PolynomialOpenModel.map.{u} stage0.val stage.val K B A
      (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
      kComm bComm aComm (Subalgebra.inclusion stage.property.2).toAlgebra
      (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
      sB kA (Subalgebra.inclusion.isScalarTower_right stage.property.2 K) coefficientIso
      (@stageScalarModel.{u} K kComm S F.left F.hom stage0) FK qF0 fK chart)
    let Y := chartPreimageModel a.left (@stageScalarModel.{u} K kComm S C.left C.hom
      (@singleScalarStage.{u} K kComm S stage0 stage)) a.right a.hom arrow
    @CoframeCertificate.{u} K kComm stage.val (stage.val ⊗[stage0.val] B)
      (inferInstanceAs (CommRing (stage.val ⊗[stage0.val] B))) Y Z
      (chartPreimageWord a.left (@stageScalarModel.{u} K kComm S C.left C.hom
        (@singleScalarStage.{u} K kComm S stage0 stage)) a.right a.hom arrow ≫
        ((@stageProjection.{u} K kComm S C.left C.hom (@singleScalarStage.{u} K kComm S stage0
        stage)) ≫ qOriginal))
      (chartPreimageChart a.left (@stageScalarModel.{u} K kComm S C.left C.hom
        (@singleScalarStage.{u} K kComm S stage0 stage)) a.right a.hom arrow) L sections unit

private theorem pullback_base_eq {A B C D : Scheme.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k k' : C ⟶ D}
    (H : IsPullback f g h k) (hk : k = k') : IsPullback f g h k' :=
  hk ▸ H

private theorem factor_cartesian {B T L : Scheme.{u}}
    (beta : T ⟶ B) (kappa : L ⟶ T) (gamma : L ⟶ B)
    (hgamma : kappa ≫ beta = gamma)
    (C : Over B) (CT : Over T) (CL : Over L)
    (qT : CT.left ⟶ C.left) (qL : CL.left ⟶ C.left)
    (hT : IsPullback qT CT.hom C.hom beta)
    (hL : IsPullback qL CL.hom C.hom gamma) :
    ∃ q : CL.left ⟶ CT.left, q ≫ qT = qL ∧
      IsPullback q CL.hom CT.hom kappa := by
  have hcomm : qL ≫ C.hom = (CL.hom ≫ kappa) ≫ beta := by
    calc
      _ = CL.hom ≫ gamma := hL.w
      _ = CL.hom ≫ (kappa ≫ beta) := congrArg (CL.hom ≫ ·) hgamma.symm
      _ = _ := (Category.assoc _ _ _).symm
  let q := hT.lift qL (CL.hom ≫ kappa) hcomm
  have hq : q ≫ qT = qL := hT.lift_fst _ _ _
  have hb : q ≫ CT.hom = CL.hom ≫ kappa := hT.lift_snd _ _ _
  exact ⟨q, hq, @DeterminantSection.intermediate_square.{u}
    B T L beta kappa gamma hgamma C CT CL qT qL q hT hL hq hb⟩

private theorem iso_cartesian_triangle {B T : Scheme.{u}}
    (beta : T ⟶ B) (C D H : Over B) (CT DT HT : Over T)
    (c : C ⟶ H) (z : D ⟶ H) (cT : CT ⟶ HT) (zT : DT ⟶ HT)
    (qC : CT.left ⟶ C.left) (qD : DT.left ⟶ D.left) (qH : HT.left ⟶ H.left)
    (hC : IsPullback qC CT.hom C.hom beta)
    (hD : IsPullback qD DT.hom D.hom beta)
    (hH : IsPullback qH HT.hom H.hom beta)
    (E : C ≅ D) (hE : E.hom ≫ z = c)
    (hc : cT.left ≫ qH = qC ≫ c.left)
    (hz : zT.left ≫ qH = qD ≫ z.left) :
    ∃ e : CT ≅ DT, e.hom ≫ zT = cT := by
  have hcomm : (qC ≫ E.hom.left) ≫ D.hom = CT.hom ≫ beta := by
    calc
      _ = qC ≫ (E.hom.left ≫ D.hom) := Category.assoc _ _ _
      _ = qC ≫ C.hom := congrArg (qC ≫ ·) E.hom.w
      _ = _ := hC.w
  let u : CT ⟶ DT :=
    Over.homMk (hD.lift (qC ≫ E.hom.left) CT.hom hcomm) (hD.lift_snd _ _ _)
  have hu : u.left ≫ qD = qC ≫ E.hom.left := hD.lift_fst _ _ _
  have hcart := @DeterminantSection.cartesian_map.{u}
    B T beta C D CT DT E.hom qC qD hC hD u hu
  let : IsIso u.left := hcart.isIso_fst_of_isIso
  let e : CT ≅ DT := Over.isoMk (asIso u.left) u.w
  have hEleft : E.hom.left ≫ z.left = c.left :=
    congrArg (fun f : C ⟶ H => f.left) hE
  refine ⟨e, ?_⟩
  apply CostructuredArrow.hom_ext
  change u.left ≫ zT.left = cT.left
  apply hH.hom_ext
  · calc
      (u.left ≫ zT.left) ≫ qH = u.left ≫ (qD ≫ z.left) := by
        rw [Category.assoc, hz]
      _ = (u.left ≫ qD) ≫ z.left := (Category.assoc _ _ _).symm
      _ = (qC ≫ E.hom.left) ≫ z.left := congrArg (· ≫ z.left) hu
      _ = qC ≫ c.left := by rw [Category.assoc, hEleft]
      _ = cT.left ≫ qH := hc.symm
  · rw [Category.assoc, zT.w, u.w, cT.w]


private theorem exists_arrow_scalar
    {K : Type u} [kComm : CommRing K] (S : Subalgebra ℤ K)
    (C F : Over (Spec (.of S))) (CK FK : Over (Spec (.of K)))
    (qC : CK.left ⟶ C.left)
    (hC : IsPullback qC CK.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qF : FK.left ⟶ F.left) (i : C ⟶ F) (iK : CK ⟶ FK)
    (hi : iK.left ≫ qF = qC ≫ i.left)
    (t : CoefficientStage S) (FT : Over (Spec (.of t.val)))
    (pF : FT.left ⟶ F.left)
    (hFT : IsPullback pF FT.hom F.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)))
    (qFT : FK.left ⟶ FT.left)
    (hFTK : IsPullback qFT FK.hom FT.hom
      (Spec.map (CommRingCat.ofHom (algebraMap t.val K))))
    (hFprojection : qFT ≫ pF = qF) :
    ∃ (e : stageScalarModel S C.hom t ⟶ FT)
      (m : CK.left ⟶ (stageScalarModel S C.hom t).left),
      IsPullback e.left
        (@stageProjection.{u} K kComm S C.left C.hom t) pF i.left ∧
      IsPullback m CK.hom (stageScalarModel S C.hom t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      m ≫ @stageProjection.{u} K kComm S C.left C.hom t = qC ∧
      iK.left ≫ qFT = m ≫ e.left ∧
      e.left ≫ pF = @stageProjection.{u} K kComm S C.left C.hom t ≫ i.left := by
  let beta := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let CT := stageScalarModel S C.hom t
  let pC := @stageProjection.{u} K kComm S C.left C.hom t
  have hCT : IsPullback pC CT.hom C.hom beta :=
    (IsPullback.of_hasPullback beta C.hom).flip
  let e : CT ⟶ FT := @DeterminantSection.cartesianLift.{u}
    (Spec (.of S)) (Spec (.of t.val)) beta C F FT pF hFT i
  have he := @DeterminantSection.cartesianLift_projection.{u}
    (Spec (.of S)) (Spec (.of t.val)) beta C F FT pF hFT i
  have hecart := @DeterminantSection.cartesian_map.{u}
    (Spec (.of S)) (Spec (.of t.val)) beta C F CT FT i pC pF hCT hFT e he
  let alpha := @FrobeniusSplitting.modelComparison.{u}
    (Spec (.of S)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    C CK qC hC
  let m := alpha.hom.left ≫ (modelScalarCone S C.hom).π.app (op t)
  have hm := @overIso_modelStage_cartesian.{u} K kComm S C.left C.hom t CK alpha
  have hp : m ≫ pC = qC := DeterminantSection.composite_projection alpha.hom.left _ _ _ qC
    (FrobeniusSplitting.scalarLeg_snd S C.hom t)
    (@FrobeniusSplitting.modelComparison_projection.{u}
      (Spec (.of S)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap S K))) C CK qC hC)
  have hTarget := @DeterminantSection.naturality_square.{u}
    (Spec (.of S)) (Spec (.of t.val)) (Spec (.of K)) beta
    (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    C F CT FT CK FK i e iK pC pF qC qF m qFT hFT he hi hp hFprojection hm.w hFTK.w
  exact ⟨e, m, hecart, hm, hp, hTarget.symm, he⟩

open ReductiveGroups DeterminantSection
open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

private theorem exists_opposition_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (M : PrefixModel G word)
    (r : G.rootBase.support) (S : Subalgebra ℤ K) (hMS : M.S ≤ S)
    (C F : Over (Spec (.of S))) [fQS : QuasiSeparatedSpace F.left]
    [fFP : LocallyOfFinitePresentation F.hom]
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal C.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom)))
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hWord : qC ≫ qOriginal = M.m₀)
    (qF : (flagVariety G).toOver.left ⟶ F.left)
    (endpoint : C ⟶ F) [endpointProper : IsProper endpoint.left]
    (hEndpoint : bsdhMap G word ≫ qF = qC ≫ endpoint.left)
    (stage0 : @CoefficientStage.{u} K kField.toCommRing S)
    (B0 : Type u) [bComm : CommRing B0] [sB : Algebra stage0.val B0]
    [bSmooth : Algebra.Smooth stage0.val B0]
    (hNontrivial : ∀ (κ : Type u) [Field κ] [Algebra stage0.val κ], Nontrivial (κ ⊗[stage0.val] B0))
    (coefficientIso : K ⊗[stage0.val] B0 ≃ₐ[K] chartAlgebra G r)
    (qF0 : (flagVariety G).toOver.left ⟶
      (@stageScalarModel.{u} K kField.toCommRing S F.left F.hom stage0).left)
    (hF0K : IsPullback qF0 (flagVariety G).toOver.hom
      (@stageScalarModel.{u} K kField.toCommRing S F.left F.hom stage0).hom
      (Spec.map (CommRingCat.ofHom (algebraMap stage0.val K))))
    (hF0projection : qF0 ≫ @stageProjection.{u} K kField.toCommRing S F.left F.hom stage0 = qF) :
    Nonempty (@CoframeStage.{u} K kField.toCommRing S stage0 B0 bComm sB
      (chartAlgebra G r) (inferInstanceAs (CommRing (chartAlgebra G r)))
      (inferInstanceAs (Algebra K (chartAlgebra G r))) coefficientIso C F
      (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
      M.cG.pt.left qOriginal endpoint
      (fun n => @matchingModule.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta n)
      (fun n => @coefficientMatchingSection.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr n)) := by
  classical
  let S0 := stage0.val
  have hS0 : S0.FG := stage0.property.1
  let beta0 := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion stage0.property.2).toRingHom)
  let F0 := @stageScalarModel.{u} K kField.toCommRing S F.left F.hom stage0
  let pF0 := @stageProjection.{u} K kField.toCommRing S F.left F.hom stage0
  have hF0 : IsPullback pF0 F0.hom F.hom beta0 :=
    (IsPullback.of_hasPullback beta0 F.hom).flip
  let : QuasiSeparatedSpace F0.left := by
    change QuasiSeparatedSpace (Limits.pullback beta0 F.hom : Scheme.{u})
    let : QuasiSeparated beta0 := by
      change QuasiSeparated (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion stage0.property.2).toRingHom))
      infer_instance
    exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd beta0 F.hom)
  let : LocallyOfFinitePresentation F0.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hF0 fFP
  have hOpen := @DeterminantSection.exists_opposition_open_stage.{u}
    K kField kClosed kZero G r S0 hS0 B0 bComm sB
    (inferInstanceAs (Algebra.FinitePresentation S0 B0)) coefficientIso
    F0 (inferInstanceAs (QuasiSeparatedSpace F0.left))
    (inferInstanceAs (LocallyOfFinitePresentation F0.hom)) qF0 hF0K
    ⟨S0, hS0, le_rfl⟩
  obtain ⟨openStage, hstartOpen, hOpen⟩ := hOpen
  let vars := ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationVars S0 B0))
  let rels := ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationRels S0 B0))
  let presentation : Algebra.Presentation S0 B0 vars rels :=
    (Algebra.Presentation.ofFinitePresentation S0 B0).reindex Equiv.ulift Equiv.ulift
  have hSection := @exists_preimage_section_stage.{u} K kField kClosed kZero
    G word M r S0 hS0 B0 bComm sB (inferInstanceAs (Module.Flat S0 B0)) coefficientIso
    vars rels (inferInstanceAs (Finite vars)) (inferInstanceAs (Finite rels)) presentation
    openStage.val openStage.property.1
  obtain ⟨R, hS0R, hOpenR, hR, hSection⟩ := hSection
  let sR : Algebra S0 R := (Subalgebra.inclusion hS0R).toAlgebra
  let towerR : IsScalarTower S0 R K := Subalgebra.inclusion.isScalarTower_right hS0R K
  let unitStage : CoefficientStage S0 := ⟨R, hR, hS0R⟩
  obtain ⟨w, hSection⟩ := hSection
  have hModel := @hOpen unitStage hOpenR
  obtain ⟨model⟩ := hModel
  let chartArrow := Arrow.mk (@PolynomialOpenModel.map.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
  let hSR : S ≤ R := stage0.property.2.trans hS0R
  let ringStage : CoefficientStage S := singleScalarStage S stage0 unitStage
  let betaRold := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom)
  have hFRold := (@PolynomialOpenModel.cartesian.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model).paste_horiz hF0
  have hScalarOld : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS0R).toRingHom) ≫
      beta0 = betaRold := by
    rw [← Spec.map_comp]
    rfl
  have hFRold := pullback_base_eq hFRold hScalarOld
  have hFRprojection : (@PolynomialOpenModel.fieldMap.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) ≫
      ((@PolynomialOpenModel.projection.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) ≫ pF0) = qF :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pF0) (@PolynomialOpenModel.field_projection.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)).trans hF0projection)
  let endpointK : M.fieldCocone.pt ⟶ (flagVariety G).toOver :=
    Over.homMk (bsdhMap G word) rfl
  have hWordR := @exists_arrow_scalar.{u} K kField.toCommRing
    S C F M.fieldCocone.pt (flagVariety G).toOver qC hC qF endpoint endpointK
    hEndpoint ringStage chartArrow.right
    ((@PolynomialOpenModel.projection.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) ≫ pF0) hFRold
    (@PolynomialOpenModel.fieldMap.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
    (@PolynomialOpenModel.field_cartesian.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) hFRprojection
  obtain ⟨endpointR, qCR, endpointRcartesian, hCR, hCRprojection,
    hEndpointR, endpointRprojection⟩ := hWordR
  let endpointRProper : IsProper endpointR.left :=
    MorphismProperty.of_isPullback (P := @IsProper) endpointRcartesian.flip endpointProper
  have hWRbase : IsPullback (@stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage)
      (stageScalarModel S C.hom ringStage).hom C.hom betaRold :=
    (IsPullback.of_hasPullback betaRold C.hom).flip
  have hOriginalR := hWRbase.paste_horiz hOriginal
  have hScalarM : betaRold ≫ Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion hMS).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hMS.trans hSR)).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hOriginalR := pullback_base_eq hOriginalR hScalarM
  have hOriginalWordR : qCR ≫ (@stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage ≫
    qOriginal) = M.m₀ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ qOriginal) hCRprojection).trans hWord)
  let : IsOpenImmersion chartArrow.hom.left :=
    (@PolynomialOpenModel.openMap.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
  have hChartCompact : CompactSpace chartArrow.left.left := by
    change CompactSpace (Spec (.of (Polynomial (R ⊗[S0] B0))))
    infer_instance
  let qChart := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (@scalarMap S0 R K B0 (chartAlgebra G r)
      (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
      kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
      sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
      sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso)))
  have hPreimage := @exists_opposition_preimage_stage.{u} K kField kClosed kZero
    G word M r R (hMS.trans hSR) chartArrow.left hChartCompact qChart
    (@PolynomialOpenModel.polynomial_cartesian.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
    (stageScalarModel S C.hom ringStage) chartArrow.right
    (@stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage ≫ qOriginal) hOriginalR
    qCR hCR hOriginalWordR
    (@PolynomialOpenModel.fieldMap.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
    (@PolynomialOpenModel.field_cartesian.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
    chartArrow.hom
    (@PolynomialOpenModel.openMap.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) endpointR endpointRProper
    (@PolynomialOpenModel.map_equation.{u} S0 R K B0 (chartAlgebra G r)
    (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing R))
    kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r)))
    sR (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra R K))
    sB (inferInstanceAs (Algebra K (chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) hEndpointR
  let Y0 := @chartPreimageModel.{u} R (inferInstanceAs (CommRing R))
    chartArrow.left
    (stageScalarModel S C.hom ringStage) chartArrow.right
    chartArrow.hom endpointR
  obtain ⟨yCompact, ySmooth, ySeparated, z, hz,
    hzWord, hWhole, hSquare, hzPolynomial⟩ := hPreimage
  let : CompactSpace Y0.left := yCompact
  let : Y0.left.IsSeparated := ySeparated
  let : Smooth Y0.hom := ySmooth
  have hCoframe := @hSection Y0.left yCompact Y0.hom ySmooth z hz
    ((@chartPreimageWord.{u} R (inferInstanceAs (CommRing R))
      chartArrow.left
    (stageScalarModel S C.hom ringStage) chartArrow.right
    chartArrow.hom endpointR) ≫ (@stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage ≫
      qOriginal)) hWhole
    (@chartPreimageChart.{u} R (inferInstanceAs (CommRing R))
      chartArrow.left
    (stageScalarModel S C.hom ringStage) chartArrow.right
    chartArrow.hom endpointR) hzPolynomial R hR
  obtain ⟨Tstage, hRT, hstartT, hTstage, hCoframe⟩ := hCoframe
  let rT : Algebra R Tstage := (Subalgebra.inclusion hRT).toAlgebra
  let towerT : IsScalarTower R Tstage K := Subalgebra.inclusion.isScalarTower_right hRT K
  let coframeStage : CoefficientStage R := ⟨Tstage, hTstage, hRT⟩
  let YT := stageScalarModel R Y0.hom coframeStage
  let qT := @stageProjection.{u} K kField.toCommRing R Y0.left Y0.hom coframeStage
  have hqT : IsPullback qT YT.hom Y0.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R Tstage))) :=
    (IsPullback.of_hasPullback _ Y0.hom).flip
  let alphaY := @FrobeniusSplitting.modelComparison.{u}
    (Spec (.of R)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (Over.mk Y0.hom) (Over.mk (preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ M.fieldCocone.pt.hom))
      z hz
  let nT := alphaY.hom.left ≫ (modelScalarCone R Y0.hom).π.app (op coframeStage)
  have hnT := @overIso_modelStage_cartesian.{u} K kField.toCommRing R Y0.left Y0.hom
    coframeStage (Over.mk (preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ M.fieldCocone.pt.hom))
      alphaY
  have hnTprojection : nT ≫ qT = z :=
    DeterminantSection.composite_projection alphaY.hom.left _ _ _ z
      (FrobeniusSplitting.scalarLeg_snd R Y0.hom coframeStage)
      (@FrobeniusSplitting.modelComparison_projection.{u} (Spec (.of R)) (Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Over.mk Y0.hom)
        (Over.mk (preimageSnd G word (𝟙 (bsdhScheme G word)) r ≫ M.fieldCocone.pt.hom)) z hz)
  let : Smooth YT.hom := MorphismProperty.of_isPullback (P := @Smooth) hqT ySmooth
  let : IsSeparated qT := MorphismProperty.of_isPullback (P := @IsSeparated) hqT.flip
    (inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R Tstage)))))
  let : YT.left.IsSeparated := separated_source qT inferInstance ySeparated
  have hFinalCoframe := @hCoframe YT.left (inferInstanceAs (YT.left.IsSeparated))
    YT.hom (inferInstanceAs (Smooth YT.hom)) qT nT hnTprojection hqT hnT
  refine ⟨@CoframeStage.mk.{u} K kField.toCommRing S stage0 B0 bComm sB
      (chartAlgebra G r) (inferInstanceAs (CommRing (chartAlgebra G r)))
      (inferInstanceAs (Algebra K (chartAlgebra G r))) coefficientIso C F
      (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
      M.cG.pt.left qOriginal endpoint
      (fun n => @matchingModule.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta n)
      (fun n => @coefficientMatchingSection.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr n) unitStage model
          endpointR endpointRprojection hNontrivial w ?_⟩
  refine @CoframeCertificate.mk.{u} K kField.toCommRing R (R ⊗[S0] B0)
    (inferInstanceAs (CommRing (R ⊗[S0] B0))) Y0 M.cG.pt.left
    (chartPreimageWord chartArrow.left (stageScalarModel S C.hom ringStage)
      chartArrow.right chartArrow.hom endpointR ≫
      ((@stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage) ≫ qOriginal))
    (chartPreimageChart chartArrow.left (stageScalarModel S C.hom ringStage)
      chartArrow.right chartArrow.hom endpointR)
    (fun n => @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta n)
    (fun n => @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr n)
    w coframeStage ?_
  exact hFinalCoframe


end SchubertGeometry.RetainedCharacter
