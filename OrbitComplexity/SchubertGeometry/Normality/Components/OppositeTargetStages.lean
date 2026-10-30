import OrbitComplexity.SchubertGeometry.Normality.Components.OppositePrimeStages
import OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages
import OrbitComplexity.SchubertGeometry.Connectedness.AppendScalarModels
import OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
import OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Morphisms from BSDH schemes to prescribed opposite Schubert models -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

namespace SchubertGeometry

universe u

open private modelComparison from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private transportOverMap transportOverMap_comparison over_source_cartesian
  genericStage_cartesian postcompose_agreement from
  OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages
open private inclusion_spec_comp from
  OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
open private cartesian_target_iso from
  OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport

private theorem map_old_base {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over T} (f : X ⟶ Y) {A D : Scheme.{u}}
    (a : A ⟶ B) (b : D ⟶ B) (qX : X.left ⟶ A) (qY : Y.left ⟶ D)
    (hX : qX ≫ a = X.hom ≫ κ) (hY : qY ≫ b = Y.hom ≫ κ) :
    f.left ≫ qY ≫ b = qX ≫ a := by
  calc
    _ = f.left ≫ (Y.hom ≫ κ) := congrArg (fun g => f.left ≫ g) hY
    _ = (f.left ≫ Y.hom) ≫ κ := (Category.assoc _ _ _).symm
    _ = X.hom ≫ κ := congrArg (fun g => g ≫ κ) f.w
    _ = _ := hX.symm

private theorem models_have_morphism {K : Type u} [hK : CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C D : Over (Spec (.of S)))
    [hCompact : CompactSpace C.left] [hQS : QuasiSeparatedSpace C.left]
    [hFP : LocallyOfFinitePresentation D.hom]
    (X Y : Over (Spec (.of K))) (f : X ⟶ Y)
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S), start ≤ t ∧
      ∃ (e : stageScalarModel S C.hom t ⟶ stageScalarModel S D.hom t)
        (qCt : X.left ⟶ (stageScalarModel S C.hom t).left)
        (qDt : Y.left ⟶ (stageScalarModel S D.hom t).left),
        IsPullback qCt X.hom (stageScalarModel S C.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback qDt Y.hom (stageScalarModel S D.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qCt ≫ e.left = f.left ≫ qDt := by
  have EC := @modelComparison (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) C X qC hC
  have ED := @modelComparison (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) D Y qD hD
  have hg := @map_old_base (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (genericScalarModel S C.hom) (genericScalarModel S D.hom)
    (transportOverMap EC ED f) C.left D.left C.hom D.hom
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) C.hom)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (g := C.hom)).symm
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (g := D.hom)).symm
  have hFT : LocallyOfFiniteType (𝟙 (Spec (.of S))) := inferInstance
  obtain ⟨t, ht, e, _hbase, he⟩ :=
    @exists_model_morphism_commuting K hK S hS C D (Over.mk (𝟙 (Spec (.of S))))
      hCompact hQS hFP hFT
      (Over.homMk C.hom (Category.comp_id C.hom))
      (Over.homMk D.hom (Category.comp_id D.hom)) (transportOverMap EC ED f) hg start
  have hCt := @over_source_cartesian (Spec (.of t.val)) (Spec (.of K))
    (stageScalarModel S C.hom t).left X (genericScalarModel S C.hom) EC
    ((modelScalarCone S C.hom).π.app (op t)) (stageScalarModel S C.hom t).hom
    (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    (@genericStage_cartesian K hK S C t)
  have hDt := @over_source_cartesian (Spec (.of t.val)) (Spec (.of K))
    (stageScalarModel S D.hom t).left Y (genericScalarModel S D.hom) ED
    ((modelScalarCone S D.hom).π.app (op t)) (stageScalarModel S D.hom t).hom
    (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    (@genericStage_cartesian K hK S D t)
  have hcomparison := @transportOverMap_comparison (Spec (.of K))
    X Y (genericScalarModel S C.hom) (genericScalarModel S D.hom) EC ED f
    (stageScalarModel S C.hom t).left (stageScalarModel S D.hom t).left
    ((modelScalarCone S C.hom).π.app (op t))
    ((modelScalarCone S D.hom).π.app (op t)) e.left he
  exact ⟨t, ht, e, EC.hom.left ≫ (modelScalarCone S C.hom).π.app (op t),
    ED.hom.left ≫ (modelScalarCone S D.hom).π.app (op t), hCt, hDt, hcomparison⟩

/-- The BSDH morphism to an opposite Schubert variety descends to a prescribed
target model after a coefficient extension. -/
theorem exists_opposite_target_stage {K : Type u} [hK : Field K]
    [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG) (D : Over (Spec (.of S)))
    [hDFP : LocallyOfFinitePresentation D.hom]
    (qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hD : IsPullback qD (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (T : Subalgebra ℤ K) (hT : T.FG) (hST : S ≤ T), start ≤ T ∧
      ∃ (C : Over (Spec (.of T)))
        (e : C ⟶ stageScalarModel S D.hom ⟨T, hT, hST⟩)
        (qC : (bsdhVariety G word).toOver.left ⟶ C.left)
        (qDt : (oppositeSchubertVariety G
          (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left ⟶
          (stageScalarModel S D.hom ⟨T, hT, hST⟩).left),
        IsProper C.hom ∧ Smooth C.hom ∧
        IsPullback qC (bsdhVariety G word).toOver.hom C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
        IsPullback qDt (oppositeSchubertVariety G
          (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom
          (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom
          (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
        qC ≫ e.left = (bsdhOppositeSchubertMap G word hred).left ≫ qDt := by
  obtain ⟨T, hsupT, hT, Y, base, m, hproper, hsmooth, _hconnected, hgood, _hfibres⟩ :=
    @exists_integral_bsdh_model K hK hAlg hChar G word (S ⊔ start) (hS.sup hstart)
  have hST : S ≤ T := le_sup_left.trans hsupT
  have hstartT : start ≤ T := le_sup_right.trans hsupT
  have hTFinite : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hTNoeth : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have hYProper : IsProper base := hproper
  have hYSmooth : Smooth base := hsmooth
  have hYCompact : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace base
  have hYLoc : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian base
  have hYQS : QuasiSeparatedSpace Y := inferInstance
  have hDtFP : LocallyOfFinitePresentation (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom := by
    change LocallyOfFinitePresentation (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) D.hom)
    infer_instance
  have ED := @modelComparison (Spec (.of S)) (Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) D
    (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver qD hD
  have hDt := @overIso_modelStage_cartesian K hK.toCommRing S D.left D.hom
    ⟨T, hT, hST⟩ (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver ED
  have descent := @models_have_morphism K hK.toCommRing T hT (Over.mk base)
      (stageScalarModel S D.hom ⟨T, hT, hST⟩) hYCompact hYQS hDtFP
      (bsdhVariety G word).toOver (oppositeSchubertVariety G
        (G.longestElement * simpleWeylWord G.rootBase word)).toOver
      (bsdhOppositeSchubertMap G word hred) m
      (ED.hom.left ≫ (modelScalarCone S D.hom).π.app (op ⟨T, hT, hST⟩)) hgood hDt
      ⟨T, hT, le_rfl⟩
  obtain ⟨t, _hstartt, e, qCt, qDt, hCt, hDtt, hcomm⟩ := descent
  have Eflat : stageScalarModel T (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom t ≅
      stageScalarModel S D.hom ⟨t.val, t.property.1, hST.trans t.property.2⟩ :=
    @scalarTowerIso (Spec (.of S)) (Spec (.of T)) (Spec (.of t.val))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) D ≪≫
      @scalarMapEq (Spec (.of S)) (Spec (.of t.val))
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom))
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (hST.trans t.property.2)).toRingHom))
        (@inclusion_spec_comp K hK.toCommRing S T t.val hST t.property.2) D
  have hDflat := @cartesian_target_iso Scheme.{u} (inferInstance : Category Scheme.{u})
    (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.left
    (stageScalarModel T (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom t).left
    (stageScalarModel S D.hom ⟨t.val, t.property.1, hST.trans t.property.2⟩).left
    (Spec (.of K)) (Spec (.of t.val)) qDt
    (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver.hom
    (stageScalarModel T (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom t).hom
    (stageScalarModel S D.hom ⟨t.val, t.property.1, hST.trans t.property.2⟩).hom
    (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))
    ((Over.forget (Spec (.of t.val))).mapIso Eflat) Eflat.hom.w hDtt
  have hcomm₀ := @postcompose_agreement Scheme.{u} (inferInstance : Category Scheme.{u})
    (bsdhVariety G word).toOver.left (stageScalarModel T base t).left
    (stageScalarModel T (stageScalarModel S D.hom ⟨T, hT, hST⟩).hom t).left
    (stageScalarModel S D.hom ⟨t.val, t.property.1, hST.trans t.property.2⟩).left
    qCt e.left ((bsdhOppositeSchubertMap G word hred).left ≫ qDt) Eflat.hom.left hcomm
  have hcomm' := hcomm₀.trans
    (Category.assoc (bsdhOppositeSchubertMap G word hred).left qDt Eflat.hom.left)
  have hCProper : IsProper (stageScalarModel T base t).hom := by
    change IsProper (pullback.fst (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion t.property.2).toRingHom)) base)
    infer_instance
  have hCSmooth : Smooth (stageScalarModel T base t).hom := by
    change Smooth (pullback.fst (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion t.property.2).toRingHom)) base)
    infer_instance
  exact ⟨t.val, t.property.1, hST.trans t.property.2, hstartT.trans t.property.2,
    stageScalarModel T base t, e ≫ Eflat.hom, qCt, qDt ≫ Eflat.hom.left,
    hCProper, hCSmooth, hCt, hDflat, hcomm'⟩



end SchubertGeometry
