import OrbitComplexity.FrobeniusSplitting.Compatible.ClosedSchemes
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelKernelStages
import OrbitComplexity.SchubertGeometry.Connectedness.PairedIncidenceModels
import OrbitComplexity.SchubertGeometry.Normality.RichardsonKernel
import OrbitComplexity.SchubertGeometry.Normality.FlagSplittingStage
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInduction
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Batteries.Tactic.Lint

/-! # Splittings on closed intersection fibres

A retained equality of closed-subscheme kernels pulls back to each prescribed
fibre. One ambient splitting preserving the two component kernels therefore
descends to that same closed target fibre.
-/

set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting ReductiveGroups
namespace SchubertGeometry

open private endpoint_proper ordinary_kernel_scalar coefficient_spec_eq from
  OrbitComplexity.SchubertGeometry.Normality.FlagSplittingStage
open private stageProjection factor_cartesian pullback_base_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages
open private cartesianLift cartesianLift_projection cartesian_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOpenStages
open private spec_triangle from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected


private theorem cartesian_kernel {X Y W Z : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (r : Z ⟶ W) (a : Z ⟶ X)
    (b : W ⟶ Y) (h : IsPullback r a b i) :
    r.ker = i.ker.comap b := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b

private theorem scalar_kernel {B T : Scheme.{u}} (coefficient : T ⟶ B)
    (D F : Over B) (j : D ⟶ F) [IsClosedImmersion j.left] :
    (chosenScalarArrow coefficient j).left.ker =
      j.left.ker.comap (pullback.snd coefficient F.hom) :=
  cartesian_kernel j.left (chosenScalarArrow coefficient j).left
    (pullback.snd coefficient D.hom) (pullback.snd coefficient F.hom)
    (chosenScalarArrow_cartesian coefficient j)

/-- A closed target with the sum of two closed kernels inherits a splitting
on each prescribed fibre from the same compatible ambient splitting. -/
theorem closedFibre_split
    {B T : Scheme.{u}} (coefficient : T ⟶ B)
    (D F DB DO : Over B) (j : D ⟶ F) (jB : DB ⟶ F) (jO : DO ⟶ F)
    [jClosed : IsClosedImmersion j.left]
    [jBClosed : IsClosedImmersion jB.left] [jOClosed : IsClosedImmersion jO.left]
    (hKernel : j.left.ker = jB.left.ker ⊔ jO.left.ker)
    (Z Dκ : Over T) (qZ : Z.left ⟶ F.left) (qD : Dκ.left ⟶ D.left)
    (hZ : IsPullback qZ Z.hom F.hom coefficient)
    (hD : IsPullback qD Dκ.hom D.hom coefficient)
    (jκ : Dκ ⟶ Z) (hInclusion : qD ≫ j.left = jκ.left ≫ qZ)
    {p : ℕ} (hp : 0 < p) (ambient : SchemeSplitting Z.left p)
    (hB : ambient.IsCompatible (pullback.fst qZ jB.left).ker)
    (hO : ambient.IsCompatible (pullback.fst qZ jO.left).ker) :
    Nonempty (SchemeSplitting Dκ.left p) := by
  have hOuter : IsPullback (jκ.left ≫ Z.hom) qD coefficient
      (j.left ≫ F.hom) := by
    simpa only [jκ.w, j.w] using hD.flip
  have hCartesian : IsPullback jκ.left qD qZ j.left :=
    hOuter.of_right hInclusion.symm hZ.flip
  let jκClosed : IsClosedImmersion jκ.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hCartesian.flip jClosed
  have hKernelκ : jκ.left.ker =
      (pullback.fst qZ jB.left).ker ⊔ (pullback.fst qZ jO.left).ker := by
    calc
      _ = (pullback.fst qZ j.left).ker := by
        rw [← hCartesian.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
      _ = j.left.ker.comap qZ :=
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j.left qZ
      _ = (jB.left.ker ⊔ jO.left.ker).comap qZ := congrArg (·.comap qZ) hKernel
      _ = jB.left.ker.comap qZ ⊔ jO.left.ker.comap qZ :=
        Scheme.IdealSheafData.comap_sup jB.left.ker jO.left.ker qZ
      _ = _ := congrArg₂ (· ⊔ ·)
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion jB.left qZ).symm
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion jO.left qZ).symm
  have hCompatible : ambient.IsCompatible jκ.left.ker :=
    hKernelκ.symm ▸ hB.sup hO
  exact ⟨@SchemeSplitting.closedOfCompatible.{u} Z.left Dκ.left p ambient jκ.left
    jκClosed hp hCompatible⟩

private theorem richardson_kernel_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (v w : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG) (D F DB DO : Over (Spec (.of S)))
    [dCompact : CompactSpace D.left] [dQS : QuasiSeparatedSpace D.left]
    [dFP : LocallyOfFinitePresentation D.hom]
    [fCompact : CompactSpace F.left] [fFP : LocallyOfFinitePresentation F.hom]
    (j : D ⟶ F) (jB : DB ⟶ F) (jO : DO ⟶ F)
    [jBClosed : IsClosedImmersion jB.left] [jOClosed : IsClosedImmersion jO.left]
    (qD : (richardsonVariety G v w).scheme ⟶ D.left)
    (qB : (schubertVariety G w).toOver.left ⟶ DB.left)
    (qO : (oppositeSchubertVariety G v).scheme ⟶ DO.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hD : IsPullback qD (richardsonVariety G v w).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hB : IsPullback qB (schubertVariety G w).toOver.hom DB.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hO : IsPullback qO (oppositeSchubertVariety G v).toSpec DO.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hj : (richardsonInclusion G v w).left ≫ qF = qD ≫ j.left)
    (hjB : (schubertInclusion G w).left ≫ qF = qB ≫ jB.left)
    (hjO : (oppositeSchubertInclusion G v).left ≫ qF = qO ≫ jO.left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t),
      let coefficient := Spec.map
        (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      (chosenScalarArrow coefficient j).left.ker =
        (chosenScalarArrow coefficient jB).left.ker ⊔
          (chosenScalarArrow coefficient jO).left.ker := by
  classical
  let I := pairedIncidenceModel jB jO
  let iI := pairedIncidenceEndpoint jB jO
  let iIClosed : IsClosedImmersion iI.left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst jB.left jO.left ≫ jB.left))
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  let : IsLocallyNoetherian I.left := LocallyOfFiniteType.isLocallyNoetherian iI.left
  let iCompact : CompactSpace I.left := QuasiCompact.compactSpace_of_compactSpace iI.left
  let iQS : QuasiSeparatedSpace I.left := inferInstance
  let iFP : LocallyOfFinitePresentation I.hom := by
    rw [← iI.w]
    infer_instance
  let IK := pairedIncidenceModel (schubertInclusion G w) (oppositeSchubertInclusion G v)
  let iIK := pairedIncidenceEndpoint (schubertInclusion G w) (oppositeSchubertInclusion G v)
  let iIKClosed : IsClosedImmersion iIK.left := by
    change IsClosedImmersion (pullback.fst (schubertInclusion G w).left
      (oppositeSchubertInclusion G v).left ≫ (schubertInclusion G w).left)
    infer_instance
  let qI := pullback.map (schubertInclusion G w).left (oppositeSchubertInclusion G v).left
    jB.left jO.left qB qO qF hjB hjO
  have hProduct := @paired_model_scalar_pullback.{u}
    (Spec (.of S)) (Spec (.of K)) (schubertVariety G w).toOver.left
    (oppositeSchubertVariety G v).scheme (flagVariety G).scheme DB.left DO.left F.left
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (schubertVariety G w).toOver.hom (oppositeSchubertVariety G v).toSpec
    (flagVariety G).toSpec DB.hom DO.hom F.hom
    (schubertInclusion G w).left (oppositeSchubertInclusion G v).left jB.left jO.left
    (schubertInclusion G w).w (oppositeSchubertInclusion G v).w jB.w jO.w
    qB qO qF hB hO hF hjB hjO
  have hI : IsPullback qI IK.hom I.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := hProduct.1
  have hIProjection : qI ≫ pullback.fst jB.left jO.left =
      pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫ qB :=
    hProduct.2.1
  have hiIK : iIK.left ≫ qF = qI ≫ iI.left := by
    change (pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫
      (schubertInclusion G w).left) ≫ qF = qI ≫ (pullback.fst jB.left jO.left ≫ jB.left)
    calc
      _ = pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫
          ((schubertInclusion G w).left ≫ qF) := Category.assoc _ _ _
      _ = pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫
          (qB ≫ jB.left) := congrArg (_ ≫ ·) hjB
      _ = (pullback.fst (schubertInclusion G w).left (oppositeSchubertInclusion G v).left ≫ qB) ≫
          jB.left := (Category.assoc _ _ _).symm
      _ = (qI ≫ pullback.fst jB.left jO.left) ≫ jB.left := congrArg (· ≫ jB.left) hIProjection.symm
      _ = _ := Category.assoc _ _ _
  have hNative : (richardsonInclusion G v w).left.ker = iIK.left.ker :=
    richardson_intersection_ker G v w
  have hRetained := @exists_closed_model_kernel_stage.{u} K kField.toCommRing S hS D I F
    dCompact dQS iCompact iQS dFP iFP (inferInstanceAs (LocallyOfFiniteType F.hom)) j iI
    (richardsonVariety G v w).toOver IK (flagVariety G).toOver
    (richardsonInclusion G v w) iIK
    (inferInstanceAs (IsClosedImmersion (richardsonInclusion G v w).left))
    iIKClosed qD qI qF hD hI hj hiIK hNative start
  obtain ⟨t, ht, hKernel⟩ := hRetained
  refine ⟨t, ht, ?_⟩
  intro coefficient
  have hEquality := hKernel (chosenScalarArrow coefficient j) (chosenScalarArrow coefficient iI)
    (chosenScalarArrow_snd coefficient j) (chosenScalarArrow_snd coefficient iI)
  have hIntersection : iI.left.ker = jB.left.ker ⊔ jO.left.ker :=
    closed_intersection_ker jB.left jO.left
  have hComap : iI.left.ker.comap (pullback.snd coefficient F.hom) =
      (jB.left.ker ⊔ jO.left.ker).comap (pullback.snd coefficient F.hom) :=
    congrArg (fun J : Scheme.IdealSheafData F.left =>
      J.comap (pullback.snd coefficient F.hom)) hIntersection
  have hSup := Scheme.IdealSheafData.comap_sup jB.left.ker jO.left.ker
    (pullback.snd coefficient F.hom)
  have hEnd := congrArg₂ (fun J J' : Scheme.IdealSheafData
      (stageScalarModel S F.hom t).left => J ⊔ J')
    (scalar_kernel coefficient DB F jB).symm (scalar_kernel coefficient DO F jO).symm
  exact hEquality.trans ((scalar_kernel coefficient I F iI).trans
    (hComap.trans (hSup.trans hEnd)))

/-- A flag splitting preserving the Schubert and opposite Schubert families
splits the Richardson target above a common coefficient bound. The source,
flag model, and closed target inclusion are retained. -/
theorem exists_split_target_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : RetainedCharacter.PrefixModel G word) (v w : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG) (CW D F : Over (Spec (.of S)))
    [cwProper : IsProper CW.hom]
    [dCompact : CompactSpace D.left] [dQS : QuasiSeparatedSpace D.left]
    [dFP : LocallyOfFinitePresentation D.hom]
    [fCompact : CompactSpace F.left] [fFP : LocallyOfFinitePresentation F.hom]
    [fSeparated : IsSeparated F.hom]
    (DOrd DOpp : G.weylGroup → Over (Spec (.of S)))
    (jOrd : ∀ z, DOrd z ⟶ F) (jOpp : ∀ z, DOpp z ⟶ F)
    [ordClosed : ∀ z, IsClosedImmersion (jOrd z).left]
    [oppClosed : ∀ z, IsClosedImmersion (jOpp z).left]
    (endpoint : CW ⟶ F) (xWord : CW.left ⟶ M.cG.pt.left)
    (r : CoefficientStage S)
    (hFlag : @flagSplittingFibres.{u} K kField kClosed kZero G word M
      S CW F DOrd jOrd DOpp jOpp endpoint xWord r)
    (j : D ⟶ F) [jClosed : IsClosedImmersion j.left]
    (qD : (richardsonVariety G v w).scheme ⟶ D.left)
    (qOrd : ∀ z, (schubertVariety G z).toOver.left ⟶ (DOrd z).left)
    (qOpp : ∀ z, (oppositeSchubertVariety G z).scheme ⟶ (DOpp z).left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hD : IsPullback qD (richardsonVariety G v w).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hOrd : ∀ z, IsPullback (qOrd z) (schubertVariety G z).toOver.hom (DOrd z).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hOpp : ∀ z, IsPullback (qOpp z) (oppositeSchubertVariety G z).toSpec (DOpp z).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hj : (richardsonInclusion G v w).left ≫ qF = qD ≫ j.left)
    (hjOrd : ∀ z, (schubertInclusion G z).left ≫ qF = qOrd z ≫ (jOrd z).left)
    (hjOpp : ∀ z, (oppositeSchubertInclusion G z).left ≫ qF = qOpp z ≫ (jOpp z).left)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t) (_ : r ≤ t),
    ∀ (κ : Type u) [_κField : Field κ] [_tκAlg : Algebra t.val κ]
      (Dκ : Over (Spec (.of κ))) (qDκ : Dκ.left ⟶ D.left)
      (_hDκ : IsPullback qDκ Dκ.hom D.hom (Spec.map (CommRingCat.ofHom
        ((algebraMap t.val κ).comp (Subalgebra.inclusion t.property.2).toRingHom))))
      (p : ℕ) [Fact p.Prime] [CharP κ p], Nonempty (SchemeSplitting Dκ.left p) := by
  classical
  obtain ⟨joint, hStartJoint, hRJoint⟩ := exists_ge_ge start r
  have hRetained := @richardson_kernel_stage.{u} K kField kClosed kZero G v w S hS
    D F (DOrd w) (DOpp v) dCompact dQS dFP fCompact fFP j (jOrd w) (jOpp v)
    (ordClosed w) (oppClosed v) qD (qOrd w) (qOpp v) qF hD (hOrd w) (hOpp v) hF
    hj (hjOrd w) (hjOpp v) joint
  obtain ⟨t, hJointT, hKernel⟩ := hRetained
  have hrt : r ≤ t := hRJoint.trans hJointT
  refine ⟨t, hStartJoint.trans hJointT, hrt, ?_⟩
  intro κ κField tκAlg Dκ qDκ hDκ p hpPrime κChar
  let beta := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let baseκ := Spec.map (CommRingCat.ofHom (algebraMap t.val κ))
  let coefficient := Spec.map (CommRingCat.ofHom
    ((algebraMap t.val κ).comp (Subalgebra.inclusion t.property.2).toRingHom))
  let FT := @stageScalarModel.{u} K kField.toCommRing S F.left F.hom t
  let DT := @stageScalarModel.{u} K kField.toCommRing S D.left D.hom t
  let Z : Over (Spec (.of κ)) := Over.mk (pullback.fst baseκ FT.hom)
  let qZt := pullback.snd baseκ FT.hom
  let qZ := qZt ≫ @stageProjection.{u} K kField.toCommRing S F.left F.hom t
  have hZt : IsPullback qZt Z.hom FT.hom baseκ :=
    (IsPullback.of_hasPullback baseκ FT.hom).flip
  have hTower : baseκ ≫ beta = coefficient :=
    @spec_triangle.{u} S t.val κ (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing t.val)) κField.toCommRing
      (Subalgebra.inclusion t.property.2).toRingHom (algebraMap t.val κ)
      ((algebraMap t.val κ).comp (Subalgebra.inclusion t.property.2).toRingHom) rfl
  have hZ : IsPullback qZ Z.hom F.hom coefficient :=
    pullback_base_eq (hZt.paste_horiz (IsPullback.of_hasPullback beta F.hom).flip) hTower
  let W : Over (Spec (.of κ)) := Over.mk (pullback.fst coefficient CW.hom)
  let qW := pullback.snd coefficient CW.hom
  have hW : IsPullback qW W.hom CW.hom coefficient :=
    (IsPullback.of_hasPullback coefficient CW.hom).flip
  let : IsProper W.hom := by
    change IsProper (pullback.fst coefficient CW.hom)
    infer_instance
  let wCompact : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  let : IsSeparated FT.hom := by
    change IsSeparated (pullback.fst beta F.hom)
    infer_instance
  let : IsSeparated Z.hom := by
    change IsSeparated (pullback.fst baseκ FT.hom)
    infer_instance
  let : Z.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from Z.hom]
    infer_instance
  let zQS : QuasiSeparatedSpace Z.left := inferInstance
  let eκ := @cartesianLift.{u} (Spec (.of S)) (Spec (.of κ)) coefficient CW F Z qZ hZ endpoint
  have heκ := @cartesianLift_projection.{u} (Spec (.of S)) (Spec (.of κ))
    coefficient CW F Z qZ hZ endpoint
  have hEndpoint := @cartesian_map.{u} (Spec (.of S)) (Spec (.of κ))
    coefficient CW F W Z endpoint qW qZ hW hZ eκ heκ
  let endpointProper : IsProper endpoint.left :=
    @endpoint_proper.{u} (Spec (.of S)) CW F cwProper fSeparated endpoint
  let eQC : QuasiCompact eκ.left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hEndpoint.flip
      (inferInstanceAs (QuasiCompact endpoint.left))
  let rκAlg : Algebra r.val κ :=
    ((algebraMap t.val κ).comp (Subalgebra.inclusion hrt).toRingHom).toAlgebra
  have hSmall := @coefficient_spec_eq.{u} K κ kField.toCommRing κField.toCommRing
    S r t hrt tκAlg
  have hWr := pullback_base_eq hW hSmall.symm
  have hZr := pullback_base_eq hZ hSmall.symm
  let x := qW ≫ xWord
  let B := fun n : Fin word.length => Over.mk (pullback.fst x (M.boundaries n).hom)
  let b := fun n : Fin word.length => pullback.snd x (M.boundaries n).hom
  have hB (n : Fin word.length) : IsPullback (B n).hom (b n) x (M.boundaries n).hom :=
    IsPullback.of_hasPullback x (M.boundaries n).hom
  have hSplitting := @hFlag κ κField rκAlg W Z wCompact zQS qW qZ hWr hZr
    eκ eQC heκ B b hB p hpPrime κChar
  obtain ⟨hIso, _cκAlg, data, _hBoundary, hOrdinary, hOpposite⟩ := hSplitting
  let : IsIso eκ.left.c := hIso
  let ambient := data.sigma.pushforward eκ.left
  have hDStage : IsPullback (@stageProjection.{u} K kField.toCommRing S D.left D.hom t)
      DT.hom D.hom beta := (IsPullback.of_hasPullback beta D.hom).flip
  have hFactor := @factor_cartesian.{u} (Spec (.of S)) (Spec (.of t.val)) (Spec (.of κ))
    beta baseκ coefficient hTower D DT Dκ
    (@stageProjection.{u} K kField.toCommRing S D.left D.hom t) qDκ hDStage hDκ
  obtain ⟨qDt, _hProjectionD, hDt⟩ := hFactor
  let jT := chosenScalarArrow beta j
  let jκ : Dκ ⟶ Z := Over.homMk
    (pullback.lift Dκ.hom (qDt ≫ jT.left)
      (hDt.w.symm.trans ((congrArg (fun a => qDt ≫ a) jT.w).symm.trans
        (Category.assoc qDt jT.left FT.hom).symm))) (pullback.lift_fst _ _ _)
  have hInclusion : qDt ≫ jT.left = jκ.left ≫ qZt := (pullback.lift_snd _ _ _).symm
  have hOrdinaryT : ambient.IsCompatible (pullback.fst qZt
      (chosenScalarArrow beta (jOrd w)).left).ker := by
    have hK := @ordinary_kernel_scalar.{u} (Spec (.of S)) (Spec (.of t.val)) Z.left
      beta (DOrd w) F (jOrd w) qZt
    exact Eq.mp (congrArg ambient.IsCompatible hK.symm) (hOrdinary w)
  have hOppositeT : ambient.IsCompatible (pullback.fst qZt
      (chosenScalarArrow beta (jOpp v)).left).ker := by
    have hK := @ordinary_kernel_scalar.{u} (Spec (.of S)) (Spec (.of t.val)) Z.left
      beta (DOpp v) F (jOpp v) qZt
    exact Eq.mp (congrArg ambient.IsCompatible hK.symm) (hOpposite v)
  let jTClosed : IsClosedImmersion jT.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (chosenScalarArrow_cartesian beta j).flip jClosed
  let jBTClosed : IsClosedImmersion (chosenScalarArrow beta (jOrd w)).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (chosenScalarArrow_cartesian beta (jOrd w)).flip (ordClosed w)
  let jOTClosed : IsClosedImmersion (chosenScalarArrow beta (jOpp v)).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (chosenScalarArrow_cartesian beta (jOpp v)).flip (oppClosed v)
  exact @closedFibre_split.{u} (Spec (.of t.val)) (Spec (.of κ)) baseκ
    DT FT (stageScalarModel S (DOrd w).hom t) (stageScalarModel S (DOpp v).hom t)
    jT (chosenScalarArrow beta (jOrd w)) (chosenScalarArrow beta (jOpp v))
    jTClosed jBTClosed jOTClosed hKernel Z Dκ qZt qDt hZt hDt jκ hInclusion p hpPrime.out.pos
      ambient hOrdinaryT hOppositeT


end SchubertGeometry
