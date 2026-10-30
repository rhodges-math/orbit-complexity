import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageSectionValues
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.FramedTransverseSplitting
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionRoots
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageGeometry
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInduction
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeSectionCoordinates
import OrbitComplexity.FrobeniusSplitting.Cartier.ChartComposition
import OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeClosedPrimes
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionModels
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Transverse compatibility on field fibres

The coframe of the prescribed arithmetic chart preimage is pulled to the same
word fibre as its section-inserted splitting. The section coefficient remains
the prescribed unit-square polynomial under this scalar extension.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open DeterminantSection

open private DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection pullSection_comp pullSection_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private wholeComparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private section_square function_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageSectionValues
open private chartCoefficientData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeSectionCoordinates
open private ProjectiveCartier.restrict_operator ProjectiveCartier.pushforward_operator from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.TwistedPushforward

private theorem inverse_section {C : Type*} [Category C] {U V W Z : C}
    (e : V ≅ W) (s : U ⟶ V) (t : U ⟶ W) (r : V ⟶ Z)
    (h : s ≫ e.hom = t) : t ≫ e.inv ≫ r = s ≫ r := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Composition preserves invertibility of the structure-sheaf maps. -/
private theorem comp_c_isIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsIso a.c] [IsIso b.c] : IsIso (a ≫ b).c := by
  change IsIso (b.c ≫ (TopCat.Presheaf.pushforward _ b.base).map a.c)
  infer_instance

/-- An isomorphism over a chart transports its preimage square. -/
private theorem preimage_iso_pullback {R : Type u} [rComm : CommRing R]
    (H W F D : Over (Spec (.of R))) (i : H ⟶ F) (j : W ⟶ F) (z : D ⟶ H)
    (E : chartPreimageModel H W F i j ≅ D)
    (hE : E.hom ≫ z = chartPreimageArrow i j) :
    ∃ b : D.left ⟶ W.left, IsPullback z.left b i.left j.left := by
  let e := (Over.forget (Spec (.of R))).mapIso E
  refine ⟨e.inv ≫ chartPreimageWord H W F i j, ?_⟩
  have hLeft : e.hom ≫ z.left = (chartPreimageArrow i j).left :=
    congrArg (fun f => f.left) hE
  refine (IsPullback.of_hasPullback i.left j.left).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Limits.pullback.fst i.left j.left = e.hom ≫ z.left
    exact hLeft.symm
  · change Limits.pullback.snd i.left j.left =
      e.hom ≫ (e.inv ≫ chartPreimageWord H W F i j)
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    rfl
  · change i.left ≫ 𝟙 _ = 𝟙 _ ≫ i.left
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change j.left ≫ 𝟙 _ = 𝟙 _ ≫ j.left
    exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem section_on_square {Y0 YT X A Z : Scheme.{u}}
    (qT : YT ⟶ Y0) (j0 : Y0 ⟶ Z) (k : A ⟶ YT) (a : A ⟶ X) (x : X ⟶ Z)
    (h : k ≫ (qT ≫ j0) = a ≫ x) (L : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ L)
    (E : (pullback qT).obj ((pullback j0).obj L) ≅
      SheafOfModules.unit YT.ringCatSheaf)
    (r : Γ(YT, ⊤))
    (hE : pullSection qT ((pullback j0).obj L) (pullSection j0 L s) ≫ E.hom =
      globalSectionsSmul (SheafOfModules.unit YT.ringCatSheaf) r) :
    ∃ F : (pullback a).obj ((pullback x).obj L) ≅ SheafOfModules.unit A.ringCatSheaf,
      pullSection a ((pullback x).obj L) (pullSection x L s) ≫ F.hom =
        globalSectionsSmul (SheafOfModules.unit A.ringCatSheaf) (k.appTop r) := by
  let E0 := ((pullbackComp qT j0).app L).symm ≪≫ E
  have h0 : pullSection (qT ≫ j0) L s ≫ E0.hom =
      globalSectionsSmul (SheafOfModules.unit YT.ringCatSheaf) r :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ E.hom) (pullSection_comp qT j0 L s)).trans hE)
  let E1 := (pullback k).mapIso E0 ≪≫ pullbackObjUnitIso k
  let comparison := wholeComparison x (qT ≫ j0) a k h L
  have hs := section_square k (qT ≫ j0) a x h L s
  have hk := pullSection_frame k ((pullback (qT ≫ j0)).obj L)
    (pullSection (qT ≫ j0) L s) E0 r h0
  refine ⟨comparison.symm ≪≫ E1, ?_⟩
  exact (inverse_section comparison _ _ E1.hom hs).trans hk

private theorem polynomial_section_pull {D T : Type u} [CommRing D] [CommRing T]
    (g : D →+* T) (P : Polynomial D) (n : ℕ) :
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g))).appTop.hom
      ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom (P ^ n)) =
        (Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom ((Polynomial.map g P) ^ n) := by
  have h := congrArg
    (fun k : CommRingCat.of (Polynomial D) ⟶ Γ(Spec (.of (Polynomial T)), ⊤) =>
      k.hom (P ^ n))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.mapRingHom g))).symm
  change (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g))).appTop.hom
      ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom (P ^ n)) =
    (Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom (Polynomial.map g (P ^ n)) at h
  simpa only [Polynomial.map_pow] using h

private theorem range_coefficient {A X Y : Scheme.{u}}
    (a : A ⟶ X) [IsOpenImmersion a] (L : X.Modules)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (E : (pullback a).obj L ≅ SheafOfModules.unit A.ringCatSheaf)
    (b : A ⟶ Y) (c : Γ(Y, ⊤))
    (hc : chartCoefficientData a L m E (b.appTop c)) :
    a.opensRange.topIso.inv
        (((m.over a.opensRange ≫ (coframeOverRange a L E).hom).val.app
          (op (Over.mk (𝟙 a.opensRange)))).hom (1 : Γ(X, a.opensRange))) =
      (a.isoOpensRange.inv ≫ b).appTop c := by
  apply (Scheme.Γ.mapIso a.isoOpensRange.op).commRingCatIsoToRingEquiv.injective
  change a.isoOpensRange.hom.appTop _ =
    a.isoOpensRange.hom.appTop ((a.isoOpensRange.inv ≫ b).appTop c)
  calc
    _ = b.appTop c := hc
    _ = (a.isoOpensRange.hom ≫ (a.isoOpensRange.inv ≫ b)).appTop c :=
      congrArg (fun f => f.appTop c) (Iso.hom_inv_id_assoc a.isoOpensRange b).symm
    _ = _ := rfl

private theorem range_square {A X Y Z : Scheme.{u}}
    (a : A ⟶ X) [IsOpenImmersion a] (b : A ⟶ Z) (f : X ⟶ Y) (k : Z ⟶ Y)
    (h : a ≫ f = b ≫ k) :
    a.opensRange.ι ≫ f = (a.isoOpensRange.inv ≫ b) ≫ k := by
  calc
    _ = (a.isoOpensRange.inv ≫ a) ≫ f :=
      congrArg (· ≫ f) (Scheme.Hom.isoOpensRange_inv_comp a).symm
    _ = a.isoOpensRange.inv ≫ (a ≫ f) := Category.assoc _ _ _
    _ = a.isoOpensRange.inv ≫ (b ≫ k) := congrArg (a.isoOpensRange.inv ≫ ·) h
    _ = _ := (Category.assoc _ _ _).symm

/-- The coframe and section equation of the same carried word model give
transverse compatibility for its prescribed section-inserted fibre splitting. -/
theorem preimageFibre_compatible
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (M : PrefixModel G word)
    {D T C : Type u} [dComm : CommRing D] [tComm : CommRing T] [cComm : CommRing C]
    (g : D →+* T) (w : Dˣ) (p : ℕ) [cChar : ExpChar C p] (hp : Odd p)
    {Y0 YT X A Flag : Scheme.{u}} (qT : YT ⟶ Y0) (j0 : Y0 ⟶ M.cG.pt.left)
    (b0 : Y0 ⟶ Spec (.of (Polynomial D))) (k : A ⟶ YT)
    (a : A ⟶ X) [hOpen : IsOpenImmersion a] (x : X ⟶ M.cG.pt.left)
    (b : A ⟶ Spec (.of (Polynomial T)))
    (hline : k ≫ (qT ≫ j0) = a ≫ x)
    (hpolynomial : k ≫ (qT ≫ b0) = b ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)))
    (base : X ⟶ Spec (.of C)) [hIso : IsIso (a.isoOpensRange.inv ≫ b).c]
    (endpoint : X ⟶ Flag) [hEndpoint : IsIso endpoint.c]
    (chart : Spec (.of (Polynomial T)) ⟶ Flag) [hChart : IsOpenImmersion chart]
    (hcomm : a ≫ endpoint = b ≫ chart) :
    let LN := @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta ((p - 1) / 2)
    let sN := @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2)
    let LX := (pullback x).obj LN
    let mX := @pullSection.{u} X M.cG.pt.left x LN sN
    ∀ (E : (pullback qT).obj ((pullback j0).obj LN) ≅
        SheafOfModules.unit YT.ringCatSheaf)
      (_hE : @pullSection.{u} YT Y0 qT ((pullback j0).obj LN)
          (@pullSection.{u} Y0 M.cG.pt.left j0 LN sN) ≫ E.hom =
        globalSectionsSmul (SheafOfModules.unit YT.ringCatSheaf)
          ((qT ≫ b0).appTop.hom ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom
            ((Polynomial.C (w : D) * Polynomial.X ^ 2) ^ ((p - 1) / 2)))))
      (data : @SectionSplitting.{u} C cComm p cChar X base LX
        (mX.app ⊤ (1 : Γ(X, ⊤)))),
      ((data.sigma.restrict a.opensRange).pushforward (a.isoOpensRange.inv ≫ b)).IsCompatible
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T)))).ker ∧
      (data.sigma.pushforward endpoint).toOperator.openPullback chart =
        ((data.sigma.restrict a.opensRange).pushforward
          (a.isoOpensRange.inv ≫ b)).toOperator := by
  intro LN sN LX mX E hE data
  obtain ⟨F, hF⟩ := @section_on_square.{u} Y0 YT X A M.cG.pt.left
    qT j0 k a x hline LN sN E
    ((qT ≫ b0).appTop.hom ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom
      ((Polynomial.C (w : D) * Polynomial.X ^ 2) ^ ((p - 1) / 2)))) hE
  have hc := @polynomial_section_pull.{u} D T dComm tComm g
    (Polynomial.C (w : D) * Polynomial.X ^ 2) ((p - 1) / 2)
  have hv := @function_square.{u} A YT (Spec (.of (Polynomial D)))
    (Spec (.of (Polynomial T))) k (qT ≫ b0) b
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g))) hpolynomial
    ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom
      ((Polynomial.C (w : D) * Polynomial.X ^ 2) ^ ((p - 1) / 2)))
    ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom
      ((Polynomial.map g (Polynomial.C (w : D) * Polynomial.X ^ 2)) ^ ((p - 1) / 2))) hc
  have hF' := hF.trans (congrArg
    (globalSectionsSmul (SheafOfModules.unit A.ringCatSheaf)) hv)
  have hRange := @ProjectiveCartier.coframeRange_section_coefficient.{u}
    A X a hOpen LX mX F
    (b.appTop ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom
      ((Polynomial.map g (Polynomial.C (w : D) * Polynomial.X ^ 2)) ^ ((p - 1) / 2)))) hF'
  have hRange' := @range_coefficient.{u} A X (Spec (.of (Polynomial T)))
    a hOpen LX mX F b
    ((Scheme.ΓSpecIso (.of (Polynomial T))).inv.hom
      ((Polynomial.map g (Polynomial.C (w : D) * Polynomial.X ^ 2)) ^ ((p - 1) / 2))) hRange
  have hP : Polynomial.map
      (tensorImageHom (Algebra.TensorProduct.lid D D)).toRingHom
      (Polynomial.C (w : D) * Polynomial.X ^ 2) =
        Polynomial.C (tensorImageHom (Algebra.TensorProduct.lid D D) (w : D)) *
          Polynomial.X ^ 2 := by
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  refine ⟨?_, ?_⟩
  · exact @DeterminantSection.coframeSplitting_transverse.{u} D D D D
      dComm dComm dComm dComm
      (inferInstanceAs (Algebra D D)) (inferInstanceAs (Algebra D D))
      (inferInstanceAs (Algebra D D)) (inferInstanceAs (Algebra D D))
      (inferInstanceAs (IsScalarTower D D D)) (inferInstanceAs (Module.Flat D D))
      (Algebra.TensorProduct.lid D D) (fun _ _ h => h)
      (Polynomial.C (w : D) * Polynomial.X ^ 2) w hP T C tComm cComm g p cChar hp
      X base LX a.opensRange (coframeOverRange a LX F) mX data.Theta
      (a.isoOpensRange.inv ≫ b) hIso data.sigma data.operator_eq hRange'
  · have h := @SchemeFrobeniusMap.openPullback_pushforward.{u}
      X Flag (Spec (.of (Polynomial T))) p data.sigma.toOperator endpoint hEndpoint
      chart hChart a.opensRange (a.isoOpensRange.inv ≫ b) hIso
      (range_square a b endpoint chart hcomm)
    calc
      _ = (data.sigma.toOperator.pushforward endpoint).openPullback chart :=
        congrArg (fun φ : SchemeFrobeniusMap Flag p => φ.openPullback chart)
          (@ProjectiveCartier.pushforward_operator.{u} X Flag p data.sigma endpoint hEndpoint)
      _ = (data.sigma.toOperator.restrict a.opensRange).pushforward
          (a.isoOpensRange.inv ≫ b) := h
      _ = (data.sigma.restrict a.opensRange).toOperator.pushforward
          (a.isoOpensRange.inv ≫ b) :=
        congrArg (fun φ : SchemeFrobeniusMap a.opensRange.toScheme p =>
          φ.pushforward (a.isoOpensRange.inv ≫ b))
          (@ProjectiveCartier.restrict_operator.{u} X p data.sigma a.opensRange).symm
      _ = _ := (@ProjectiveCartier.pushforward_operator.{u} a.opensRange.toScheme
        (Spec (.of (Polynomial T))) p (data.sigma.restrict a.opensRange)
          (a.isoOpensRange.inv ≫ b) hIso).symm

open private separated_source stageProjection CoframeCertificate CoframeCertificate.stage
  CoframeStage
  pullback_base_eq factor_cartesian iso_cartesian_triangle exists_arrow_scalar from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages

open private DeterminantSection.naturality_square DeterminantSection.cartesian_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOpenStages

/-- A prescribed comparison of the coefficient algebra gives the coefficient
Cartesian square and the equation for its polynomial zero section. -/
private theorem zero_coefficient_square
    {R κ D T : Type u} [rComm : CommRing R] [κComm : CommRing κ]
    [dComm : CommRing D] [tComm : CommRing T]
    [rκ : Algebra R κ] [rD : Algebra R D] [κT : Algebra κ T]
    [rT : Algebra R T] [tower : IsScalarTower R κ T]
    (e : κ ⊗[R] D ≃ₐ[κ] T)
    (g : D →+* T)
    (hg : g = e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : D →ₐ[R] κ ⊗[R] D).toRingHom) :
    IsPullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (algebraMap κ T)))
      (Spec.map (CommRingCat.ofHom (algebraMap R D)))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ∧
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)) =
      Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : D))) := by
  refine ⟨?_, @polynomial_zero_map.{u} D T dComm tComm g⟩
  subst g
  exact (@isPullback_affineModel.{u} R κ D T rComm κComm dComm tComm
    rκ rD κT rT tower e).flip

/-- A retained isomorphism over the coefficient chart transports its preimage
square to prescribed Cartesian field models. -/
private theorem preimage_chart_transport
    {R κ : Type u} [rComm : CommRing R] [κComm : CommRing κ] [rκ : Algebra R κ]
    (T : Scheme.{u})
    (beta : T ⟶ Spec (.of R)) (kappa : Spec (.of κ) ⟶ T)
    (gamma : Spec (.of κ) ⟶ Spec (.of R))
    (hGamma : gamma = Spec.map (CommRingCat.ofHom (algebraMap R κ)))
    (hCoeff : kappa ≫ beta = gamma)
    (HR ER FR DR : Over (Spec (.of R)))
    (iR : HR ⟶ FR) (jR : ER ⟶ FR) (zR : DR ⟶ HR)
    (CL DL HL : Over T) (cL : CL ⟶ HL) (zL : DL ⟶ HL)
    (qCL : CL.left ⟶ (chartPreimageModel HR ER FR iR jR).left)
    (qDL : DL.left ⟶ DR.left) (qHL : HL.left ⟶ HR.left)
    (hCL : IsPullback qCL CL.hom (chartPreimageModel HR ER FR iR jR).hom beta)
    (hDL : IsPullback qDL DL.hom DR.hom beta)
    (hHL : IsPullback qHL HL.hom HR.hom beta)
    (hcL : cL.left ≫ qHL = qCL ≫ (chartPreimageArrow iR jR).left)
    (hzL : zL.left ≫ qHL = qDL ≫ zR.left)
    (zeroIso : CL ≅ DL) (hZero : zeroIso.hom ≫ zL = cL)
    (Hκ Eκ Z Dκ : Over (Spec (.of κ)))
    (chartκ : Hκ ⟶ Z) (jκ : Eκ ⟶ Z) (zκ : Dκ ⟶ Hκ)
    (qH : Hκ.left ⟶ HR.left) (qER : Eκ.left ⟶ ER.left)
    (qZR : Z.left ⟶ FR.left) (qD : Dκ.left ⟶ DR.left)
    (hHκ : IsPullback qH Hκ.hom HR.hom gamma)
    (hER : IsPullback qER Eκ.hom ER.hom gamma)
    (hZR : IsPullback qZR Z.hom FR.hom gamma)
    (hD : IsPullback qD Dκ.hom DR.hom gamma)
    (hChart : chartκ.left ≫ qZR = qH ≫ iR.left)
    (hInclusion : jκ.left ≫ qZR = qER ≫ jR.left)
    (hz : zκ.left ≫ qH = qD ≫ zR.left) :
    ∃ zeroChart : Dκ.left ⟶ Eκ.left,
      IsPullback zκ.left zeroChart chartκ.left jκ.left := by
  subst gamma
  let Cκ := chartPreimageModel Hκ Eκ Z chartκ jκ
  let cκ := chartPreimageArrow chartκ jκ
  obtain ⟨qC, hqC, _hqCWord, hC⟩ := @exists_chartPreimage_scalar.{u} R κ
    rComm κComm (inferInstanceAs (Algebra R κ))
    HR ER FR Hκ Eκ Z iR jR chartκ jκ qH qER qZR hHκ hER hZR
    hChart hInclusion Cκ.left
    (chartPreimageChart Hκ Eκ Z chartκ jκ)
    (chartPreimageWord Hκ Eκ Z chartκ jκ) (IsPullback.of_hasPullback _ _)
  obtain ⟨pC, hpC, hCp⟩ := @factor_cartesian.{u}
    (Spec (.of R)) T (Spec (.of κ)) beta kappa (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
      hCoeff
    (chartPreimageModel HR ER FR iR jR) CL Cκ qCL qC hCL hC
  obtain ⟨pD, hpD, hDp⟩ := @factor_cartesian.{u}
    (Spec (.of R)) T (Spec (.of κ)) beta kappa (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
      hCoeff
    DR DL Dκ qDL qD hDL hD
  obtain ⟨pH, hpH, hHp⟩ := @factor_cartesian.{u}
    (Spec (.of R)) T (Spec (.of κ)) beta kappa (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
      hCoeff
    HR HL Hκ qHL qH hHL hHκ
  have hcField := @DeterminantSection.naturality_square.{u}
    (Spec (.of R)) T (Spec (.of κ)) beta kappa
    (chartPreimageModel HR ER FR iR jR) HR CL HL Cκ Hκ
    (chartPreimageArrow iR jR) cL cκ qCL qHL qC qH pC pH
    hHL hcL hqC.symm hpC hpH hCp.w hHp.w
  have hzField := @DeterminantSection.naturality_square.{u}
    (Spec (.of R)) T (Spec (.of κ)) beta kappa
    DR HR DL HL Dκ Hκ zR zL zκ qDL qHL qD qH pD pH
    hHL hzL hz hpD hpH hDp.w hHp.w
  obtain ⟨Efield, hEfield⟩ := @iso_cartesian_triangle.{u}
    T (Spec (.of κ)) kappa CL DL HL Cκ Dκ Hκ
    cL zL cκ zκ pC pD pH hCp hDp hHp zeroIso hZero
    hcField.symm hzField.symm
  exact @preimage_iso_pullback.{u} κ κComm Hκ Eκ Z Dκ chartκ jκ zκ
    Efield hEfield


private theorem indexed_cartesian {I : Type*} {B T : Scheme.{u}}
    (X : I → Over T) {i j : I} (h : i = j) (D : Over B)
    (q : (X j).left ⟶ D.left) (κ : T ⟶ B)
    (hq : IsPullback q (X j).hom D.hom κ) :
    IsPullback (eqToHom (congrArg (fun z => (X z).left) h) ≫ q)
      (X i).hom D.hom κ := by
  cases h
  simpa only [eqToHom_refl, Category.id_comp] using hq

private theorem exists_integral_simple_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (r : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) (E : Over (Spec (.of S)))
    [eFP : LocallyOfFinitePresentation E.hom] [eCompact : CompactSpace E.left]
    (qE : (oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem
      (DeterminantSection.oppositionSimple G r))).scheme ⟶ E.left)
    (hE : IsPullback qE (oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem
      (DeterminantSection.oppositionSimple G r))).toSpec E.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ t : CoefficientStage S, start ≤ t ∧
      ∀ (κ : Type u) [Field κ] [Algebra t.val κ]
        (Eκ : Over (Spec (.of κ))) (bE : Eκ.left ⟶ E.left)
        (_hEκ : IsPullback bE Eκ.hom E.hom
          (Spec.map (CommRingCat.ofHom ((algebraMap t.val κ).comp
            (Subalgebra.inclusion t.property.2).toRingHom)))), IsIntegral Eκ.left := by
  obtain ⟨resolution, hred, hprod⟩ :=
    (weylCoxeterSystem G.rootBase).exists_isReduced
      (G.longestElement * RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G r))
  have hprod' := hprod.trans (weylCoxeterSystem_wordProd G.rootBase resolution)
  have htarget : G.longestElement * simpleWeylWord G.rootBase resolution =
      RootPairing.weylGroup.ofIdx G.rootSystem (DeterminantSection.oppositionSimple G r) := by
    rw [← hprod', ← mul_assoc]
    have hsq : G.longestElement * G.longestElement = 1 := longestWeylElement_sq G.rootBase
    rw [hsq, one_mul]
  let qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase resolution)).scheme ⟶ E.left :=
    eqToHom (congrArg (fun w => (oppositeSchubertVariety G w).scheme) htarget) ≫ qE
  have hD := @indexed_cartesian G.weylGroup (Spec (.of S)) (Spec (.of K))
    (fun w => (oppositeSchubertVariety G w).toOver)
    (G.longestElement * simpleWeylWord G.rootBase resolution)
    (RootPairing.weylGroup.ofIdx G.rootSystem (DeterminantSection.oppositionSimple G r))
    htarget E qE (Spec.map (CommRingCat.ofHom (algebraMap S K))) hE
  have hIntegral := @exists_opposite_closed_primes.{u} K kField kClosed kZero G
    resolution hred S hS E eFP eCompact qD hD start.val start.property.1
  obtain ⟨T, hT, hstart, hST, hFields⟩ := hIntegral
  refine ⟨⟨T, hT, hST⟩, hstart, ?_⟩
  intro κ κField tκAlg Eκ bE hEκ
  exact (@hFields κ κField tκAlg Eκ bE hEκ).1

/-- Transverse compatibility in a nonempty polynomial chart determines
compatibility with the integral divisor containing that chart. -/
private theorem preimageFibre_image_compatible
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (M : PrefixModel G word)
    {D T C : Type u} [dComm : CommRing D] [tComm : CommRing T] [cComm : CommRing C] [Nontrivial T]
    (g : D →+* T) (w : Dˣ) (p : ℕ) [cChar : ExpChar C p] (hp : Odd p)
    {Y0 YT X A Flag : Scheme.{u}} (qT : YT ⟶ Y0) (j0 : Y0 ⟶ M.cG.pt.left)
    (b0 : Y0 ⟶ Spec (.of (Polynomial D))) (k : A ⟶ YT)
    (a : A ⟶ X) [hOpen : IsOpenImmersion a] (x : X ⟶ M.cG.pt.left)
    (b : A ⟶ Spec (.of (Polynomial T)))
    (hline : k ≫ (qT ≫ j0) = a ≫ x)
    (hpolynomial : k ≫ (qT ≫ b0) = b ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)))
    (base : X ⟶ Spec (.of C)) [hIso : IsIso (a.isoOpensRange.inv ≫ b).c]
    (endpoint : X ⟶ Flag) [hEndpoint : IsIso endpoint.c]
    (chart : Spec (.of (Polynomial T)) ⟶ Flag) [hChart : IsOpenImmersion chart]
    [hChartQC : QuasiCompact chart]
    (hcomm : a ≫ endpoint = b ≫ chart)
    (Div : Scheme.{u}) [hDivIntegral : IsIntegral Div]
    (divisor : Div ⟶ Flag) [hDivQC : QuasiCompact divisor]
    (zeroChart : Spec (.of T) ⟶ Div)
    (hDiv : IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T))))
      zeroChart chart divisor) :
    let LN := @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta ((p - 1) / 2)
    let sN := @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2)
    let LX := (pullback x).obj LN
    let mX := @pullSection.{u} X M.cG.pt.left x LN sN
    ∀ (E : (pullback qT).obj ((pullback j0).obj LN) ≅
        SheafOfModules.unit YT.ringCatSheaf)
      (_hE : @pullSection.{u} YT Y0 qT ((pullback j0).obj LN)
          (@pullSection.{u} Y0 M.cG.pt.left j0 LN sN) ≫ E.hom =
        globalSectionsSmul (SheafOfModules.unit YT.ringCatSheaf)
          ((qT ≫ b0).appTop.hom ((Scheme.ΓSpecIso (.of (Polynomial D))).inv.hom
            ((Polynomial.C (w : D) * Polynomial.X ^ 2) ^ ((p - 1) / 2)))))
      (data : @SectionSplitting.{u} C cComm p cChar X base LX
        (mX.app ⊤ (1 : Γ(X, ⊤)))),
      (data.sigma.pushforward endpoint).IsCompatible divisor.ker := by
  intro LN sN LX mX E hE data
  obtain ⟨hker, hoperator⟩ := @preimageFibre_compatible.{u}
    K kField kClosed kZero G word M D T C dComm tComm cComm
    g w p cChar hp Y0 YT X A Flag qT j0 b0 k a hOpen x b hline hpolynomial
    base hIso endpoint hEndpoint chart hChart hcomm E hE data
  exact @SchemeSplitting.isCompatible_ker_of_dense_chart.{u}
    Flag Div (Spec (.of (Polynomial T))) (Spec (.of T)) p
    hDivIntegral (inferInstanceAs (Nonempty (Spec (.of T))))
    (data.sigma.pushforward endpoint) divisor hDivQC
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : T)))) zeroChart chart
    hChart hChartQC hDiv
    ((data.sigma.restrict a.opensRange).pushforward (a.isoOpensRange.inv ≫ b))
    hoperator hker

/-- The coframe and a boundary isomorphism give compatibility on prescribed field fibres. -/
private theorem coframe_field_compatible
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (M : PrefixModel G word)
    (R : Subalgebra ℤ K) (D : Type u) [dComm : CommRing D] [rD : Algebra R D]
    (C F E : Over (Spec (.of R))) (x : C.left ⟶ M.cG.pt.left)
    (iR : @polynomialModel.{u} R D (inferInstanceAs (CommRing R)) dComm rD ⟶ F)
    [iROpen : IsOpenImmersion iR.left] (arrow : C ⟶ F)
    (jR : E ⟶ F) [jRClosed : IsClosedImmersion jR.left] (w : Dˣ) :
    let HR := (Arrow.mk iR).left
    let Y0 := chartPreimageModel HR C F iR arrow
    let j0 := chartPreimageWord HR C F iR arrow ≫ x
    let b0 := chartPreimageChart HR C F iR arrow
    let LN := fun n : ℕ => @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta n
    let sections := fun n : ℕ => @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr n
    ∀ (coframe : @CoframeCertificate.{u} K kField.toCommRing R D dComm Y0
        M.cG.pt.left j0 b0 LN sections w)
      (_hBoundary : boundaryModelAgreement R (chartPreimageArrow iR jR)
        (@polynomialZero.{u} R D (inferInstanceAs (CommRing R)) dComm rD) (CoframeCertificate.stage
          coframe)),
    ∃ (bound : CoefficientStage R) (_ : CoframeCertificate.stage coframe ≤ bound),
    ∀ (κ : Type u) [_κField : Field κ] [_rκAlg : Algebra R κ] [_bκAlg : Algebra bound.val κ]
      (_hCoeff : Spec.map (CommRingCat.ofHom (algebraMap bound.val κ)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion bound.property.2).toRingHom) =
          Spec.map (CommRingCat.ofHom (algebraMap R κ)))
      [_hNontrivial : Nontrivial (κ ⊗[R] D)]
      (W Z Eκ : Over (Spec (.of κ))) [_zQS : QuasiSeparatedSpace Z.left]
      [_eIntegral : IsIntegral Eκ.left]
      (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left) (qE : Eκ.left ⟶ E.left)
      (_hW : IsPullback qW W.hom C.hom (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      (_hZ : IsPullback qZ Z.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      (_hE : IsPullback qE Eκ.hom E.hom (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      (e : W ⟶ Z) [_eIso : IsIso e.left.c] (_he : e.left ≫ qZ = qW ≫ arrow.left)
      (jκ : Eκ ⟶ Z) (_hjκ : jκ.left ≫ qZ = qE ≫ jR.left)
      (xκ : W.left ⟶ M.cG.pt.left) (_hx : qW ≫ x = xκ)
      (p : ℕ) (C0 : Type u) [cComm : CommRing C0] [cChar : ExpChar C0 p]
      (_hp : Odd p) (base : W.left ⟶ Spec (.of C0)),
      let LX := (pullback xκ).obj (LN ((p - 1) / 2))
      let mX := @pullSection.{u} W.left M.cG.pt.left xκ
        (LN ((p - 1) / 2)) (sections ((p - 1) / 2))
      ∀ data : @SectionSplitting.{u} C0 cComm p cChar W.left base LX
        (mX.app ⊤ (1 : Γ(W.left, ⊤))),
        (data.sigma.pushforward e.left).IsCompatible jκ.left.ker := by
  intro HR Y0 j0 b0 LN sections coframe hBoundary
  rcases coframe with ⟨coframeStage, frames⟩
  obtain ⟨bound, hFrameBound, zeroIso, hZeroTriangle⟩ := hBoundary
  refine ⟨bound, hFrameBound, ?_⟩
  intro κ κField rκAlg bκAlg hCoeff hNontrivial W Z Eκ zQS eIntegral
    qW qZ qE hW hZ hE e eIso he jκ hjκ xκ hx p C0 cComm cChar hp base LX mX data
  let kR := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  let YT := stageScalarModel R Y0.hom coframeStage
  let qT := @stageProjection.{u} K kField.toCommRing R Y0.left Y0.hom coframeStage
  have hqT : IsPullback qT YT.hom Y0.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion coframeStage.property.2).toRingHom)) :=
    (IsPullback.of_hasPullback _ Y0.hom).flip
  let Tκ := κ ⊗[R] D
  let tComm : CommRing Tκ := inferInstance
  let Hκ := @polynomialModel.{u} κ Tκ κField.toCommRing tComm
    (inferInstanceAs (Algebra κ Tκ))
  let eκ := @AlgEquiv.refl.{u,u} κ Tκ
    (@CommRing.toCommSemiring κ κField.toCommRing)
    (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm))
    (inferInstanceAs (Algebra κ Tκ))
  let g : @RingHom D Tκ
      (@Semiring.toNonAssocSemiring D
        (@CommSemiring.toSemiring D (@CommRing.toCommSemiring D dComm)))
      (@Semiring.toNonAssocSemiring Tκ
        (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm))) :=
    eκ.toRingHom.comp (Algebra.TensorProduct.includeRight : D →ₐ[R] Tκ).toRingHom
  let qH := Spec.map (@CommRingCat.ofHom
    (@Polynomial D (@CommSemiring.toSemiring D (@CommRing.toCommSemiring D dComm)))
    (@Polynomial Tκ (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm)))
    (@Polynomial.commRing D dComm) (@Polynomial.commRing Tκ tComm)
    (@Polynomial.mapRingHom D Tκ
      (@CommSemiring.toSemiring D (@CommRing.toCommSemiring D dComm))
      (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm)) g))
  obtain ⟨_, _, _, hPolynomial⟩ := @exists_scalar_polynomial_square.{u} R κ D Tκ
    (inferInstanceAs (CommRing R)) κField.toCommRing
    dComm tComm
    rκAlg (inferInstanceAs (Algebra R D)) (inferInstanceAs (Algebra κ Tκ))
    eκ
  have hHκ : IsPullback qH Hκ.hom
      HR.hom kR := by
    exact hPolynomial
  have hChartBase : (qH ≫ iR.left) ≫ F.hom = Hκ.hom ≫ kR := by
    calc
      _ = qH ≫ (iR.left ≫ F.hom) := Category.assoc _ _ _
      _ = qH ≫ HR.hom := congrArg (qH ≫ ·) iR.w
      _ = _ := hHκ.w
  let chartκ : Hκ ⟶ Z := Over.homMk
    (hZ.lift (qH ≫ iR.left) Hκ.hom hChartBase) (hZ.lift_snd _ _ _)
  have hChartProjection : chartκ.left ≫ qZ = qH ≫ iR.left := hZ.lift_fst _ _ _
  have hChartSquare := @DeterminantSection.cartesian_map.{u}
    (Spec (.of R)) (Spec (.of κ)) kR
    HR F Hκ Z iR qH qZ hHκ hZ chartκ hChartProjection
  let chartOpen : IsOpenImmersion chartκ.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hChartSquare.flip iROpen
  let A := chartPreimageModel Hκ W Z chartκ e
  let a := chartPreimageWord Hκ W Z chartκ e
  let b := chartPreimageChart Hκ W Z chartκ e
  have hASquare : IsPullback b a chartκ.left e.left :=
    IsPullback.of_hasPullback _ _
  obtain ⟨qA, hqAChart, hqAWord, hA⟩ := @exists_chartPreimage_scalar.{u} R κ
    (inferInstanceAs (CommRing R)) κField.toCommRing rκAlg
    HR C F Hκ W Z iR arrow chartκ e qH qW qZ
    hHκ hW hZ hChartProjection he A.left
    b a hASquare
  let frameκAlg : Algebra coframeStage.val κ :=
    ((algebraMap bound.val κ).comp (Subalgebra.inclusion hFrameBound).toRingHom).toAlgebra
  let kT := Spec.map (CommRingCat.ofHom (@algebraMap coframeStage.val κ _ _ frameκAlg))
  have hCoeffT : kT ≫ Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion coframeStage.property.2).toRingHom) = kR := by
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap bound.val κ)) ≫
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion bound.property.2).toRingHom) := by
            rw [← Spec.map_comp, ← Spec.map_comp]
            rfl
      _ = _ := hCoeff
  obtain ⟨k, hk, _hkSquare⟩ := @factor_cartesian.{u}
    (Spec (.of R)) (Spec (.of coframeStage.val)) (Spec (.of κ))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion coframeStage.property.2).toRingHom))
    kT kR hCoeffT Y0 YT A qT qA hqT hA
  have hline : k ≫ (qT ≫ j0) = a ≫ xκ := by
    calc
      _ = (k ≫ qT) ≫ j0 := (Category.assoc _ _ _).symm
      _ = qA ≫ j0 := congrArg (fun m => m ≫ j0) hk
      _ = (qA ≫ chartPreimageWord HR C F iR arrow) ≫ x := (Category.assoc _ _ _).symm
      _ = (a ≫ qW) ≫ x := congrArg (fun m => m ≫ x) hqAWord
      _ = a ≫ (qW ≫ x) := Category.assoc _ _ _
      _ = _ := congrArg (a ≫ ·) hx
  have hpolynomial : k ≫ (qT ≫ b0) = b ≫ qH := by
    calc
      _ = (k ≫ qT) ≫ b0 := (Category.assoc _ _ _).symm
      _ = qA ≫ b0 := congrArg (fun m => m ≫ b0) hk
      _ = _ := hqAChart
  have aOpen : IsOpenImmersion a :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hASquare chartOpen
  let : IsOpenImmersion a := aOpen
  have hbIso : IsIso b.c := @CharacterLine.openPullback_c_isIso.{u}
    A.left W.left Hκ.left Z.left b a chartκ.left e.left chartOpen hASquare eIso
  have haInv : IsIso a.isoOpensRange.inv.c :=
    PresheafedSpace.c_isIso_of_iso a.isoOpensRange.inv.toPshHom
  have hRangeIso : IsIso (a.isoOpensRange.inv ≫ b).c :=
    @comp_c_isIso.{u} a.opensRange.toScheme A.left Hκ.left
      a.isoOpensRange.inv b haInv hbIso
  let zR := @polynomialZero.{u} R D (inferInstanceAs (CommRing R)) dComm rD
  let DR := (Arrow.mk zR).left
  let zκ := @polynomialZero.{u} κ Tκ κField.toCommRing tComm
    (inferInstanceAs (Algebra κ Tκ))
  let Dκ := (Arrow.mk zκ).left
  let qD := Spec.map (CommRingCat.ofHom g)
  obtain ⟨hD, hz⟩ := @zero_coefficient_square.{u} R κ D Tκ
    (inferInstanceAs (CommRing R)) κField.toCommRing dComm tComm rκAlg rD
    (inferInstanceAs (Algebra κ Tκ)) (inferInstanceAs (Algebra R Tκ))
    (inferInstanceAs (IsScalarTower R κ Tκ)) eκ g rfl
  let beta := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion bound.property.2).toRingHom)
  let kappa := Spec.map (CommRingCat.ofHom (algebraMap bound.val κ))
  let Cpre := chartPreimageModel HR E F iR jR
  let cR := chartPreimageArrow iR jR
  let CL := stageScalarModel R Cpre.hom bound
  let DL := stageScalarModel R DR.hom bound
  let HL := stageScalarModel R HR.hom bound
  let cL := chosenScalarArrow beta cR
  let zL := chosenScalarArrow beta zR
  let qCL := Limits.pullback.snd beta Cpre.hom
  let qDL := Limits.pullback.snd beta DR.hom
  let qHL := Limits.pullback.snd beta HR.hom
  have hCL : IsPullback qCL CL.hom Cpre.hom beta := (IsPullback.of_hasPullback _ _).flip
  have hDL : IsPullback qDL DL.hom DR.hom beta := (IsPullback.of_hasPullback _ _).flip
  have hHL : IsPullback qHL HL.hom HR.hom beta := (IsPullback.of_hasPullback _ _).flip
  have hcL : cL.left ≫ qHL = qCL ≫ cR.left := chosenScalarArrow_snd beta cR
  have hzL : zL.left ≫ qHL = qDL ≫ zR.left := chosenScalarArrow_snd beta zR
  have hZero : zeroIso.hom ≫ zL = cL := by
    apply Over.OverMorphism.ext
    exact hZeroTriangle cL zL hcL hzL
  obtain ⟨zeroChart, hZeroChart⟩ := @preimage_chart_transport.{u}
    R κ (inferInstanceAs (CommRing R)) κField.toCommRing rκAlg
    (Spec (.of bound.val)) beta kappa kR rfl hCoeff
    HR E F DR iR jR zR CL DL HL cL zL qCL qDL qHL hCL hDL hHL hcL hzL
    zeroIso hZero Hκ Eκ Z Dκ chartκ jκ zκ qH qE qZ qD
    hHκ hE hZ hD hChartProjection hjκ hz
  have hDivSquare := @DeterminantSection.cartesian_map.{u}
    (Spec (.of R)) (Spec (.of κ)) kR E F Eκ Z jR qE qZ hE hZ jκ hjκ
  let jκClosed : IsClosedImmersion jκ.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hDivSquare.flip jRClosed
  let jκQC : QuasiCompact jκ.left := inferInstance
  have hHCompact : CompactSpace Hκ.left :=
    @PrimeSpectrum.compactSpace
      (@Polynomial Tκ (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm)))
      (@CommRing.toCommSemiring
        (@Polynomial Tκ (@CommSemiring.toSemiring Tκ (@CommRing.toCommSemiring Tκ tComm)))
        (@Polynomial.commRing Tκ tComm))
  let hChartQC : QuasiCompact chartκ.left :=
    @quasiCompact_of_compactSpace Hκ.left Z.left chartκ.left hHCompact zQS
  obtain ⟨frame, hFrame⟩ := frames ((p - 1) / 2)
  exact @preimageFibre_image_compatible.{u}
    K kField kClosed kZero G word M D Tκ C0 dComm tComm cComm hNontrivial
    g w p cChar hp Y0.left YT.left W.left A.left Z.left
    qT j0 b0 k a aOpen xκ b hline hpolynomial base hRangeIso
    e.left eIso chartκ.left chartOpen hChartQC hASquare.w.symm
    Eκ.left eIntegral jκ.left jκQC zeroChart hZeroChart frame hFrame data

open private exists_opposition_stage from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages
open private FrobeniusSplitting.modelComparison FrobeniusSplitting.modelComparison_projection from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private FrobeniusSplitting.scalarLeg_snd from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
open private DeterminantSection.composite_projection from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChartModels

/-- After coefficient extension, the prescribed section-inserted splitting
preserves the same opposite simple Schubert divisor on every field fibre. -/
theorem exists_opposition_compatible_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : PrefixModel G word) (r : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) (hMS : M.S ≤ S)
    (C F E : Over (Spec (.of S)))
    [fCompact : CompactSpace F.left] [fQS : QuasiSeparatedSpace F.left]
    [fFP : LocallyOfFinitePresentation F.hom]
    [eFP : LocallyOfFinitePresentation E.hom]
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal C.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom)))
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hWord : qC ≫ qOriginal = M.m₀)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (endpoint : C ⟶ F) [endpointProper : IsProper endpoint.left]
    (hEndpoint : bsdhMap G word ≫ qF = qC ≫ endpoint.left)
    (j : E ⟶ F) [jClosed : IsClosedImmersion j.left]
    (qE : (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).scheme ⟶ E.left)
    (hE : IsPullback qE (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).toSpec E.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hj : (oppositeSchubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).left ≫ qF =
        qE ≫ j.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
    ∀ (κ : Type u) [_κField : Field κ] [_tκAlg : Algebra t.val κ]
      (W Z Eκ : Over (Spec (.of κ))) [_zQS : QuasiSeparatedSpace Z.left]
      (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left) (bE : Eκ.left ⟶ E.left)
      (_hW : IsPullback qW W.hom C.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap t.val κ).comp
          (Subalgebra.inclusion t.property.2).toRingHom))))
      (_hZ : IsPullback qZ Z.hom F.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap t.val κ).comp
          (Subalgebra.inclusion t.property.2).toRingHom))))
      (_hEκ : IsPullback bE Eκ.hom E.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap t.val κ).comp
          (Subalgebra.inclusion t.property.2).toRingHom))))
      (e : W ⟶ Z) [_eIso : IsIso e.left.c]
      (_he : e.left ≫ qZ = qW ≫ endpoint.left)
      (jκ : Eκ ⟶ Z) (_hjκ : jκ.left ≫ qZ = bE ≫ j.left)
      (xκ : W.left ⟶ M.cG.pt.left) (_hxκ : qW ≫ qOriginal = xκ)
      (p : ℕ) [_pPrime : Fact p.Prime] [_κChar : CharP κ p] (_hp : Odd p),
      let L := (Scheme.Modules.pullback xκ).obj
        (@matchingModule.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta ((p - 1) / 2))
      let m := @pullSection.{u} W.left M.cG.pt.left xκ
        (@matchingModule.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta ((p - 1) / 2))
        (@coefficientMatchingSection.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2))
      ∀ (cκAlg : Algebra (ULift.{u} (ZMod p)) κ)
        (data : @SectionSplitting.{u} (ULift.{u} (ZMod p))
          (@Field.toCommRing (ULift.{u} (ZMod p))
            (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
          (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) W.left
          (W.hom ≫ Spec.map (CommRingCat.ofHom
            (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
          (m.app ⊤ (1 : Γ(W.left, ⊤)))),
        (data.sigma.pushforward e.left).IsCompatible jκ.left.ker := by
  classical
  let : CompactSpace E.left := QuasiCompact.compactSpace_of_compactSpace j.left
  have hIntegralData := @exists_integral_simple_stage.{u} K kField kClosed kZero
    G r S hS E eFP (inferInstanceAs (CompactSpace E.left)) qE hE start
  obtain ⟨integralStage, hstartI, hIntegral⟩ := hIntegralData
  have hCoefficient := @DeterminantSection.exists_opposition_coefficient_model.{u}
    K kField kClosed kZero G r integralStage.val integralStage.property.1
  obtain ⟨S0, hIS0, hS0, B, bComm, sB, bSmooth, hCoefficientIso, hNontrivial⟩ := hCoefficient
  let : CommRing B := bComm
  let : Algebra S0 B := sB
  let : Algebra.Smooth S0 B := bSmooth
  obtain ⟨coefficientIso⟩ := hCoefficientIso
  let stage0 : CoefficientStage S := ⟨S0, hS0, integralStage.property.2.trans hIS0⟩
  let F0 := @stageScalarModel.{u} K kField.toCommRing S F.left F.hom stage0
  let pF0 := @stageProjection.{u} K kField.toCommRing S F.left F.hom stage0
  let alphaF := @FrobeniusSplitting.modelComparison.{u}
    (Spec (.of S)) (Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    F (flagVariety G).toOver qF hF
  let qF0 := alphaF.hom.left ≫ (modelScalarCone S F.hom).π.app (op stage0)
  have hF0K := @overIso_modelStage_cartesian.{u} K kField.toCommRing S F.left F.hom
    stage0 (flagVariety G).toOver alphaF
  have hF0projection : qF0 ≫ pF0 = qF :=
    DeterminantSection.composite_projection alphaF.hom.left _ _ _ qF
      (FrobeniusSplitting.scalarLeg_snd S F.hom stage0)
      (@FrobeniusSplitting.modelComparison_projection.{u} (Spec (.of S)) (Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) F (flagVariety G).toOver qF hF)
  have hArithmetic := @exists_opposition_stage.{u} K kField kClosed kZero
    G word M r S hMS C F fQS fFP qOriginal hOriginal qC hC hWord qF endpoint endpointProper
    hEndpoint stage0 B bComm sB bSmooth hNontrivial coefficientIso qF0 hF0K hF0projection
  obtain ⟨state⟩ := hArithmetic
  rcases state with ⟨stage, chart, arrow, hArrow, hNontrivial, w, coframe⟩
  let sR : Algebra stage0.val stage.val := (Subalgebra.inclusion stage.property.2).toAlgebra
  let towerR : IsScalarTower stage0.val stage.val K :=
    Subalgebra.inclusion.isScalarTower_right stage.property.2 K
  let ringStage := @singleScalarStage.{u} K kField.toCommRing S stage0 stage
  let aR := Arrow.mk (@PolynomialOpenModel.map.{u}
    stage0.val stage.val K B (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
  let D := type_of% w.val
  let pFR := (@PolynomialOpenModel.projection.{u} stage0.val stage.val K B
    (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
  let : Algebra stage0.val stage.val := sR
  let dComm : CommRing D := inferInstance
  let LN := fun n : ℕ => @matchingModule.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta n
  let sections := fun n : ℕ => @coefficientMatchingSection.{u} M.S M.J
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr n
  let CR := stageScalarModel S C.hom ringStage
  let pCR := @stageProjection.{u} K kField.toCommRing S C.left C.hom ringStage
  let Y0 := chartPreimageModel aR.left CR aR.right aR.hom arrow
  let j0 := chartPreimageWord aR.left CR aR.right aR.hom arrow ≫ (pCR ≫ qOriginal)
  let b0 := chartPreimageChart aR.left CR aR.right aR.hom arrow
  change @CoframeCertificate.{u} K kField.toCommRing stage.val D dComm Y0
    M.cG.pt.left j0 b0 LN sections w at coframe
  let coframeStage := CoframeCertificate.stage coframe
  have iROpen : IsOpenImmersion aR.hom.left := (@PolynomialOpenModel.openMap.{u}
    stage0.val stage.val K B (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
  let beta0 := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion stage0.property.2).toRingHom)
  let betaR := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion ringStage.property.2).toRingHom)
  have hF0 : IsPullback pF0 F0.hom F.hom beta0 :=
    (IsPullback.of_hasPullback beta0 F.hom).flip
  have hFRold0 := (@PolynomialOpenModel.cartesian.{u} stage0.val stage.val K B
    (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
      chart).paste_horiz hF0
  have hScalarOld : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion stage.property.2).toRingHom) ≫
      beta0 = betaR := by
    rw [← Spec.map_comp]
    rfl
  have hFRold := pullback_base_eq hFRold0 hScalarOld
  have hFRprojection : (@PolynomialOpenModel.fieldMap.{u} stage0.val stage.val K B
    (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
      ≫
      (pFR ≫ pF0) = qF :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pF0) (@PolynomialOpenModel.field_projection.{u} stage0.val stage.val K B
        (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
      chart)).trans hF0projection)
  have hDivisor := @exists_arrow_scalar.{u} K kField.toCommRing S E F
    (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).toOver
    (flagVariety G).toOver qE hE qF j
    (oppositeSchubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))) hj
    ringStage aR.right (pFR ≫ pF0) hFRold
    (@PolynomialOpenModel.fieldMap.{u} stage0.val stage.val K B (DeterminantSection.chartAlgebra G
      r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
    (@PolynomialOpenModel.field_cartesian.{u} stage0.val stage.val K B
      (DeterminantSection.chartAlgebra G r)
    (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
    kField.toCommRing bComm (inferInstanceAs (CommRing (DeterminantSection.chartAlgebra G r)))
    sR (inferInstanceAs (Algebra stage0.val K)) (inferInstanceAs (Algebra stage.val K))
    sB (inferInstanceAs (Algebra K (DeterminantSection.chartAlgebra G r))) towerR coefficientIso F0
    (flagVariety G).toOver qF0 (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left chart)
      hFRprojection
  obtain ⟨jR, qERK, hjRcart, hERK, hERKprojection, hjRK, hjRprojection⟩ := hDivisor
  let ER := @stageScalarModel.{u} K kField.toCommRing S E.left E.hom ringStage
  let pER := @stageProjection.{u} K kField.toCommRing S E.left E.hom ringStage
  have hERold : IsPullback pER ER.hom E.hom betaR :=
    (IsPullback.of_hasPullback betaR E.hom).flip
  let jRClosed : IsClosedImmersion jR.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hjRcart.flip jClosed
  let erFP : LocallyOfFinitePresentation ER.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hERold eFP
  have hBoundary := @exists_opposition_boundary_stage.{u} K kField kClosed kZero
    G r stage0.val stage.val stage.property.1 B bComm sR sB
    (inferInstanceAs (Algebra.FinitePresentation stage0.val B)) towerR coefficientIso F0 qF0 chart
    ER erFP jR jRClosed qERK hERK hjRK coframeStage
  have hFieldData := @coframe_field_compatible.{u} K kField kClosed kZero
    G word M stage.val D dComm (inferInstanceAs (Algebra stage.val D))
    CR aR.right ER (pCR ≫ qOriginal) aR.hom iROpen arrow jR jRClosed w coframe hBoundary
  obtain ⟨boundaryStage, _hCoframeBoundary, hFields⟩ := hFieldData
  let t := @singleScalarStage.{u} K kField.toCommRing S ringStage boundaryStage
  have hstart : start ≤ t := hstartI.trans (hIS0.trans
    (stage.property.2.trans boundaryStage.property.2))
  have hRt : stage.val ≤ t.val := boundaryStage.property.2
  have hIt : integralStage.val ≤ t.val := hIS0.trans
    (stage.property.2.trans boundaryStage.property.2)
  refine ⟨t, hstart, ?_⟩
  intro κ κField tκAlg W Z Eκ zQS qW qZ bE hW hZ hEκ e eIso he jκ hjκ xκ hxκ p pPrime κChar hp
    LX mX cκAlg data
  let rκAlg : Algebra stage.val κ :=
    ((algebraMap t.val κ).comp (Subalgebra.inclusion hRt).toRingHom).toAlgebra
  let : Algebra stage.val κ := rκAlg
  let kR := Spec.map (CommRingCat.ofHom (algebraMap stage.val κ))
  let gamma := Spec.map (CommRingCat.ofHom
    ((algebraMap t.val κ).comp (Subalgebra.inclusion t.property.2).toRingHom))
  have hCoeff : kR ≫ betaR = gamma := by
    rw [← Spec.map_comp]
    rfl
  have hCbase : IsPullback pCR CR.hom C.hom betaR :=
    (IsPullback.of_hasPullback betaR C.hom).flip
  obtain ⟨qX, hqX, hX⟩ := @factor_cartesian.{u}
    (Spec (.of S)) (Spec (.of stage.val)) (Spec (.of κ)) betaR kR gamma hCoeff
    C CR W pCR qW hCbase hW
  obtain ⟨qZR, hqZR, hZR⟩ := @factor_cartesian.{u}
    (Spec (.of S)) (Spec (.of stage.val)) (Spec (.of κ)) betaR kR gamma hCoeff
    F aR.right Z (pFR ≫ pF0) qZ hFRold hZ
  obtain ⟨qER, hqER, hER⟩ := @factor_cartesian.{u}
    (Spec (.of S)) (Spec (.of stage.val)) (Spec (.of κ)) betaR kR gamma hCoeff
    E ER Eκ pER bE hERold hEκ
  have heR := @DeterminantSection.naturality_square.{u}
    (Spec (.of S)) (Spec (.of stage.val)) (Spec (.of κ)) betaR kR C F CR aR.right W Z
    endpoint arrow e pCR (pFR ≫ pF0) qW qZ qX qZR
    hFRold hArrow he hqX hqZR hX.w hZR.w
  have hjField := @DeterminantSection.naturality_square.{u}
    (Spec (.of S)) (Spec (.of stage.val)) (Spec (.of κ)) betaR kR E F ER aR.right Eκ Z
    j jR jκ pER (pFR ≫ pF0) bE qZ qER qZR
    hFRold hjRprojection hjκ hqER hqZR hER.w hZR.w
  have hx : qX ≫ (pCR ≫ qOriginal) = xκ :=
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ qOriginal) hqX)).trans hxκ
  let bκAlg : Algebra boundaryStage.val κ := tκAlg
  have hBoundCoeff : Spec.map (CommRingCat.ofHom (@algebraMap boundaryStage.val κ _ _ bκAlg)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion boundaryStage.property.2).toRingHom) = kR :=
        by
    rw [← Spec.map_comp]
    rfl
  let iκAlg : Algebra integralStage.val κ :=
    ((algebraMap t.val κ).comp (Subalgebra.inclusion hIt).toRingHom).toAlgebra
  have hIntegralCoeff :
      Spec.map (CommRingCat.ofHom ((@algebraMap integralStage.val κ _ _ iκAlg).comp
        (Subalgebra.inclusion integralStage.property.2).toRingHom)) = gamma := by
    rfl
  have eIntegral : IsIntegral Eκ.left :=
    @hIntegral κ κField iκAlg Eκ bE (pullback_base_eq hEκ hIntegralCoeff.symm)
  let sκAlg : Algebra stage0.val κ :=
    ((algebraMap stage.val κ).comp (Subalgebra.inclusion stage.property.2).toRingHom).toAlgebra
  let : Algebra stage0.val κ := sκAlg
  let towerκ : IsScalarTower stage0.val stage.val κ := IsScalarTower.of_algebraMap_eq' rfl
  let _ := @hNontrivial κ κField sκAlg
  have hTensor : Nontrivial (κ ⊗[stage.val] D) :=
    (@tensorCancelEquiv.{u} stage0.val stage.val κ
      (inferInstanceAs (CommRing stage0.val)) (inferInstanceAs (CommRing stage.val))
      κField.toCommRing (Subalgebra.inclusion stage.property.2).toAlgebra
      rκAlg sκAlg towerκ B bComm sB).toEquiv.nontrivial
  exact @hFields κ κField rκAlg bκAlg hBoundCoeff hTensor
    W Z Eκ zQS eIntegral qX qZR qER hX hZR hER e eIso heR.symm jκ hjField.symm
    xκ hx p (ULift.{u} (ZMod p))
    (@Field.toCommRing (ULift.{u} (ZMod p)) (inferInstanceAs (Field (ULift.{u} (ZMod p)))))
    (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) hp
    (W.hom ≫ Spec.map (CommRingCat.ofHom
      (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) data

end SchubertGeometry.RetainedCharacter
