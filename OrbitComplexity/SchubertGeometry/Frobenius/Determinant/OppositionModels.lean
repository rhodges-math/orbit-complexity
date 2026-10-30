import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageGeometry
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
import Batteries.Tactic.Lint

/-! # Coefficient models of opposite boundary ideals -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open GroupActions ReductiveGroups FrobeniusSplitting

namespace SchubertGeometry.DeterminantSection

open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private FrobeniusSplitting.RetainedCharacter.scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

/-- Two coefficient models become isomorphic over a common coefficient extension,
with their maps agreeing after any prescribed scalar pullback. -/
def boundaryModelAgreement {K : Type u} [CommRing K] (R : Subalgebra ℤ K)
    {C D H : Over (Spec (.of R))} (c : C ⟶ H) (z : D ⟶ H)
    (start : CoefficientStage R) : Prop :=
  ∃ (t : CoefficientStage R) (_ : start ≤ t)
    (E : stageScalarModel R C.hom t ≅ stageScalarModel R D.hom t),
    ∀ (it : stageScalarModel R C.hom t ⟶ stageScalarModel R H.hom t)
      (zt : stageScalarModel R D.hom t ⟶ stageScalarModel R H.hom t),
    it.left ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) H.hom =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) C.hom ≫
          c.left →
    zt.left ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) H.hom =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) D.hom ≫
          z.left →
    E.hom.left ≫ zt.left = it.left

private theorem boundary_triangle
    {B T : Scheme.{u}} {C D F : Over B} {C' D' F' : Over T}
    (κ : T ⟶ B) (E : C' ≅ D') (i : C ⟶ F) (j : D ⟶ F)
    (i' : C' ⟶ F') (j' : D' ⟶ F')
    (qC : C'.left ⟶ C.left) (qD : D'.left ⟶ D.left)
    (qF : F'.left ⟶ F.left)
    (hF : IsPullback qF F'.hom F.hom κ)
    (hi : i'.left ≫ qF = qC ≫ i.left)
    (hj : j'.left ≫ qF = qD ≫ j.left)
    (hE : E.hom.left ≫ qD ≫ j.left = qC ≫ i.left) :
    E.hom.left ≫ j'.left = i'.left := by
  apply hF.hom_ext
  · calc
      _ = E.hom.left ≫ (j'.left ≫ qF) := Category.assoc _ _ _
      _ = E.hom.left ≫ (qD ≫ j.left) := congrArg (E.hom.left ≫ ·) hj
      _ = qC ≫ i.left := hE
      _ = _ := hi.symm
  · calc
      _ = E.hom.left ≫ D'.hom := by rw [Category.assoc, j'.w]
      _ = C'.hom := E.hom.w
      _ = _ := i'.w.symm

private theorem boundary_iso_stage
    {K : Type u} [kComm : CommRing K] (R : Subalgebra ℤ K) (hR : R.FG)
    {H W F : Over (Spec (.of R))} (i : H ⟶ F) (j : W ⟶ F)
    (D : Over (Spec (.of R))) (z : D ⟶ H)
    (hOpen : IsOpenImmersion i.left) (hClosed : IsClosedImmersion j.left)
    (hCompact : CompactSpace H.left) (hQS : QuasiSeparatedSpace H.left)
    (hWFP : LocallyOfFinitePresentation W.hom)
    (hDCompact : CompactSpace D.left) (hDQS : QuasiSeparatedSpace D.left)
    (hDFP : LocallyOfFinitePresentation D.hom) (hHFT : LocallyOfFiniteType H.hom)
    {HK WK FK : Over (Spec (.of K))} (iK : HK ⟶ FK) (jK : WK ⟶ FK)
    (DK : Over (Spec (.of K))) (b : DK ⟶ HK)
    (hJClosed : IsClosedImmersion jK.left) (hBClosed : IsClosedImmersion b.left)
    (qH : HK.left ⟶ H.left) (qW : WK.left ⟶ W.left)
    (qF : FK.left ⟶ F.left) (qD : DK.left ⟶ D.left)
    (hH : IsPullback qH HK.hom H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hW : IsPullback qW WK.hom W.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hF : IsPullback qF FK.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hD : IsPullback qD DK.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hi : iK.left ≫ qF = qH ≫ i.left)
    (hj : jK.left ≫ qF = qW ≫ j.left)
    (hz : b.left ≫ qH = qD ≫ z.left)
    (hkernel : (pullback.fst iK.left jK.left).ker = b.left.ker)
    (start : CoefficientStage R) :
    boundaryModelAgreement R (SchubertGeometry.RetainedCharacter.chartPreimageArrow i j)
      z start := by
  have cProps := SchubertGeometry.RetainedCharacter.chartPreimage_closed_properties
    i j hOpen hClosed hCompact hQS hWFP
  let c := SchubertGeometry.RetainedCharacter.chartPreimageArrow i j
  obtain ⟨qC, hqC, _, hC⟩ :=
    @SchubertGeometry.RetainedCharacter.exists_chartPreimage_scalar.{u}
      R K (inferInstanceAs (CommRing R)) kComm (inferInstanceAs (Algebra R K))
      H W F HK WK FK i j iK jK qH qW qF hH hW hF hi hj _
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let a := SchubertGeometry.RetainedCharacter.chartPreimageArrow iK jK
  let : IsClosedImmersion jK.left := hJClosed
  have ha : IsClosedImmersion a.left := by
    change IsClosedImmersion (pullback.fst iK.left jK.left)
    infer_instance
  obtain ⟨t, ht, E, hE⟩ := @exists_closed_ideal_iso_stage.{u} K kComm
    R hR (SchubertGeometry.RetainedCharacter.chartPreimageModel H W F i j) D H
    cProps.1 cProps.2.1 hDCompact hDQS cProps.2.2 hDFP hHFT c z
    (SchubertGeometry.RetainedCharacter.chartPreimageModel HK WK FK iK jK) DK HK
    a b ha hBClosed qC qD qH hC hD hqC.symm hz hkernel start
  refine ⟨t, ht, E, ?_⟩
  intro it zt hit hzt
  exact @boundary_triangle.{u} (Spec (.of R)) (Spec (.of t.val))
    (SchubertGeometry.RetainedCharacter.chartPreimageModel H W F i j) D H
    (stageScalarModel R
      (SchubertGeometry.RetainedCharacter.chartPreimageModel H W F i j).hom t)
    (stageScalarModel R D.hom t) (stageScalarModel R H.hom t)
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
    E c z it zt
    (pullback.snd _ (SchubertGeometry.RetainedCharacter.chartPreimageModel H W F i j).hom)
    (pullback.snd _ D.hom) (pullback.snd _ H.hom)
    (IsPullback.of_hasPullback _ H.hom).flip hit hzt hE

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K)

/-- The opposite simple boundary on a polynomial open model becomes its
coefficient zero section after a coefficient extension. -/
theorem exists_opposition_boundary_stage
    (r : G.rootBase.support) (S R : Subalgebra ℤ K) (hR : R.FG)
    (B : Type u) [bComm : CommRing B] [sR : Algebra S R] [sB : Algebra S B]
    [bFP : Algebra.FinitePresentation S B] [tower : IsScalarTower S R K]
    (e : K ⊗[S] B ≃ₐ[K] (chartAlgebra G r)) (F : Over (Spec (.of S)))
    (qF : (flagVariety G).toOver.left ⟶ F.left)
    (model : @PolynomialOpenModel.{u} S R K B (chartAlgebra G r) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs (CommRing
      (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB
      (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left)
    (W : Over (Spec (.of R))) [wFP : LocallyOfFinitePresentation W.hom]
    (j : W ⟶ (@PolynomialOpenModel.flagModel.{u} S R K B (chartAlgebra G r) (inferInstanceAs
      (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs
      (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R
      K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)) [jClosed :
      IsClosedImmersion j.left]
    (qW : (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).toOver.left ⟶ W.left)
    (hW : IsPullback qW (oppositeSchubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G r))).toOver.hom W.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hj : (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G
      r))).left ≫ (@PolynomialOpenModel.fieldMap.{u} S R K B (chartAlgebra G r) (inferInstanceAs
      (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs
      (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R
      K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) = qW ≫ j.left)
    (start : CoefficientStage R) :
    boundaryModelAgreement R
      (SchubertGeometry.RetainedCharacter.chartPreimageArrow (@PolynomialOpenModel.map.{u} S R K B
        (chartAlgebra G r) (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R))
        kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r))) sR (inferInstanceAs
        (Algebra S K)) (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K (chartAlgebra
        G r))) tower e F (flagVariety G).toOver qF (@oppositionPolynomialMap.{u} K kField kClosed
        kZero G r).left model) j)
      (@polynomialZero.{u} R (R ⊗[S] B) (inferInstanceAs (CommRing R))
        (inferInstanceAs (CommRing (R ⊗[S] B)))
        (inferInstanceAs (Algebra R (R ⊗[S] B)))) start := by
  have hOpen : IsOpenImmersion (@PolynomialOpenModel.map.{u} S R K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm
    (inferInstanceAs (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K))
    (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F
    (flagVariety G).toOver qF (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left
    model).left := (@PolynomialOpenModel.openMap.{u} S R K B (chartAlgebra G r) (inferInstanceAs
    (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs (CommRing
    (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB
    (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
    (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
  let z := @polynomialZero.{u} R (R ⊗[S] B) (inferInstanceAs (CommRing R))
    (inferInstanceAs (CommRing (R ⊗[S] B)))
    (inferInstanceAs (Algebra R (R ⊗[S] B)))
  have hProps := @polynomial_model_properties.{u}
    R (R ⊗[S] B) (inferInstanceAs (CommRing R))
    (inferInstanceAs (CommRing (R ⊗[S] B)))
    (inferInstanceAs (Algebra R (R ⊗[S] B)))
    (inferInstanceAs (Algebra.FinitePresentation R (R ⊗[S] B)))
  let : LocallyOfFinitePresentation _ := hProps.2.2
  have dCompact : CompactSpace ((algSpec (.of R)).obj (op (CommAlgCat.of R (R ⊗[S] B)))).left := by
    change CompactSpace (Spec (.of (R ⊗[S] B)))
    infer_instance
  have dQS : QuasiSeparatedSpace ((algSpec (.of R)).obj (op (CommAlgCat.of R (R ⊗[S] B)))).left :=
    by
    change QuasiSeparatedSpace (Spec (.of (R ⊗[S] B)))
    infer_instance
  have dFP : LocallyOfFinitePresentation ((algSpec (.of R)).obj (op (CommAlgCat.of R (R ⊗[S]
    B)))).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[S] B))))
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hH := (@PolynomialOpenModel.polynomial_cartesian.{u} S R K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm
    (inferInstanceAs (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K))
    (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F
    (flagVariety G).toOver qF (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
  have hD := @coefficient_scalar_cartesian.{u} S R K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm
      (inferInstanceAs (CommRing (chartAlgebra G r))) sR
    (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K
      (chartAlgebra G r))) tower e
  have hz := @polynomial_zero_map.{u} (R ⊗[S] B) (chartAlgebra G r) (inferInstanceAs (CommRing (R
    ⊗[S] B))) (inferInstanceAs (CommRing (chartAlgebra G r)))
    (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B (chartAlgebra G r) (inferInstanceAs
    (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs (CommRing
    (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB
    (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e)
  let b := @polynomialZero.{u} K (chartAlgebra G r) kField.toCommRing
    (inferInstanceAs (CommRing (chartAlgebra G r))) (inferInstanceAs (Algebra K (chartAlgebra G r)))
  have hb : IsClosedImmersion b.left :=
    IsClosedImmersion.spec_of_surjective _ (fun x => ⟨Polynomial.C x, Polynomial.eval_C⟩)
  let chartArrow := CategoryTheory.Arrow.mk (@PolynomialOpenModel.map.{u} S R K B (chartAlgebra G r)
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm
    (inferInstanceAs (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K))
    (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F
    (flagVariety G).toOver qF (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
  let H := chartArrow.left
  let Fmodel := chartArrow.right
  exact @boundary_iso_stage.{u} K kField.toCommRing R hR
    H W Fmodel
    chartArrow.hom j ((algSpec (.of R)).obj (op (CommAlgCat.of R (R ⊗[S] B)))) z hOpen jClosed
      hProps.1 hProps.2.1 wFP
    dCompact dQS dFP (inferInstanceAs (LocallyOfFiniteType (@polynomialModel.{u} R (R ⊗[S] B)
      (inferInstanceAs (CommRing R)) (inferInstanceAs (CommRing (R ⊗[S] B))) (inferInstanceAs
      (Algebra R (R ⊗[S] B)))).hom))
    (@polynomialModel.{u} K (chartAlgebra G r) kField.toCommRing (inferInstanceAs (CommRing
      (chartAlgebra G r))) (inferInstanceAs (Algebra K (chartAlgebra G r))))
      (oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G
      r))).toOver (flagVariety G).toOver (@oppositionPolynomialMap.{u} K kField kClosed kZero G r)
      (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G
      r)))
    ((algSpec (.of K)).obj (op (CommAlgCat.of K (chartAlgebra G r)))) b (inferInstanceAs
      (IsClosedImmersion (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem
      (oppositionSimple G r))).left)) hb
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B (chartAlgebra G r) (inferInstanceAs
        (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs
        (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra
        R K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e))))
    qW (@PolynomialOpenModel.fieldMap.{u} S R K B (chartAlgebra G r) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs (CommRing
      (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB
      (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model)
    (Spec.map (CommRingCat.ofHom (@FrobeniusSplitting.RetainedCharacter.scalarMap S R K B
      (chartAlgebra G r) (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R))
      kField.toCommRing bComm (inferInstanceAs (CommRing (chartAlgebra G r))) sR (inferInstanceAs
      (Algebra S K)) (inferInstanceAs (Algebra R K)) sB (inferInstanceAs (Algebra K (chartAlgebra G
      r))) tower e)))
    hH hW (@PolynomialOpenModel.field_cartesian.{u} S R K B (chartAlgebra G r) (inferInstanceAs
      (CommRing S)) (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs
      (CommRing (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R
      K)) sB (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) hD
    (@PolynomialOpenModel.map_equation.{u} S R K B (chartAlgebra G r) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R)) kField.toCommRing bComm (inferInstanceAs (CommRing
      (chartAlgebra G r))) sR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) sB
      (inferInstanceAs (Algebra K (chartAlgebra G r))) tower e F (flagVariety G).toOver qF
      (@oppositionPolynomialMap.{u} K kField kClosed kZero G r).left model) hj hz
    (@oppositionPolynomial_kernel.{u} K kField kClosed kZero G r) start

end SchubertGeometry.DeterminantSection
