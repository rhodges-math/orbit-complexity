import OrbitComplexity.SchubertGeometry.Connectedness.InitialPairedSource
import OrbitComplexity.SchubertGeometry.FlagVariety.Proper
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Initial source and flag models over one coefficient ring

The smooth paired source and the flag variety are first descended separately.
Extending both models to the join of their coefficient rings gives Cartesian
comparisons over one ring, while retaining smoothness of the source.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry

universe u

open private model_scalar_original from
  OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

private theorem comparison_at_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (t : CoefficientStage S) (N : Over (Spec (.of K))) (q : N.left ⟶ X)
    (hq : IsPullback q N.hom a (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    ∃ qt : N.left ⟶ (stageScalarModel S a t).left,
      IsPullback qt N.hom (stageScalarModel S a t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      qt ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) a = q := by
  let E := hq.flip.isoOverPullback
  let qt := E.hom.left ≫ (modelScalarCone S a).π.app (op t)
  refine ⟨qt, overIso_modelStage_cartesian S a t N E, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => E.hom.left ≫ k) (model_scalar_original S a t)).trans
      hq.flip.isoOverPullback_hom_left_comp_snd)

private theorem common_source_flag
    {K : Type u} [CommRing K]
    (X Y : Over (Spec (.of K)))
    (S T : Subalgebra ℤ K) (hT : T.FG)
    (C : Over (Spec (.of S))) (F : Over (Spec (.of T)))
    [CompactSpace C.left] [CompactSpace F.left]
    [Smooth C.hom] [LocallyOfFinitePresentation C.hom]
    [LocallyOfFinitePresentation F.hom]
    (qC : X.left ⟶ C.left) (qF : Y.left ⟶ F.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF Y.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (start : CoefficientStage S) :
    ∃ (r : CoefficientStage S), start ≤ r ∧ ∃ hTR : T ≤ r.val,
      let j : CoefficientStage T := ⟨r.val, r.property.1, hTR⟩
      let CR := stageScalarModel S C.hom r
      let FR := stageScalarModel T F.hom j
      ∃ (rC : X.left ⟶ CR.left) (rF : Y.left ⟶ FR.left),
        AlgebraicGeometry.IsNoetherian CR.left ∧
        AlgebraicGeometry.IsNoetherian FR.left ∧
        Smooth CR.hom ∧ LocallyOfFinitePresentation CR.hom ∧
        LocallyOfFinitePresentation FR.hom ∧
        IsPullback rC X.hom CR.hom
          (Spec.map (CommRingCat.ofHom (algebraMap r.val K))) ∧
        IsPullback rF Y.hom FR.hom
          (Spec.map (CommRingCat.ofHom (algebraMap r.val K))) ∧
        rC ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)) C.hom = qC ∧
        rF ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTR).toRingHom)) F.hom = qF := by
  let R := start.val ⊔ T
  have hR : R.FG := start.property.1.sup hT
  let i : CoefficientStage S := ⟨R, hR, start.property.2.trans le_sup_left⟩
  refine ⟨i, (show start.val ≤ R from le_sup_left), le_sup_right, ?_⟩
  intro j CR FR
  let : CompactSpace CR.left := by
    change CompactSpace ((modelScalarStages S C.hom).obj (op i))
    infer_instance
  let : CompactSpace FR.left := by
    change CompactSpace ((modelScalarStages T F.hom).obj (op j))
    infer_instance
  let : Smooth CR.hom := by
    change Smooth (pullback.fst _ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation CR.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation FR.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ F.hom)
    infer_instance
  let : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  have hnC := (finiteType_int_scheme_properties CR.hom).1
  have hnF := (finiteType_int_scheme_properties FR.hom).1
  obtain ⟨rC, hrC, hOldC⟩ := @comparison_at_stage.{u} K inferInstance S C.left C.hom i X qC hC
  obtain ⟨rF, hrF, hOldF⟩ := @comparison_at_stage.{u} K inferInstance T F.left F.hom j Y qF hF
  exact ⟨rC, rF, hnC, hnF, inferInstance, inferInstance, inferInstance,
    hrC, hrF, hOldC, hOldF⟩

private theorem affine_variety_diagonal {K : Type u} [Field K]
    (V : GroupActions.Variety K) :
    IsAffineHom (pullback.diagonal (terminal.from V.scheme)) := by
  let : IsSeparated (terminal.from V.scheme) := by
    rw [← terminal.comp_from V.toSpec]
    infer_instance
  infer_instance

/-- Two reduced words construct a smooth paired source and a flag model
over one finitely generated coefficient ring, with both Cartesian
comparisons and Noetherian model schemes. -/
theorem exists_initial_flag_source
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    ∃ (R : Subalgebra ℤ K) (C F : Over (Spec (.of R)))
      (qC : (pairedBSDHSource G a b).left ⟶ C.left)
      (qF : (flagVariety G).scheme ⟶ F.left),
      R.FG ∧ AlgebraicGeometry.IsNoetherian C.left ∧
      AlgebraicGeometry.IsNoetherian F.left ∧
      Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
      LocallyOfFinitePresentation F.hom ∧
      IsPullback qC (pairedBSDHSource G a b).hom C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsPullback qF (flagVariety G).toSpec F.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨S, C, qC, hS, hcompact, _hqs, hsmooth, hfp, hC⟩ :=
    exists_initial_paired_source G a b ha hb
  let : CompactSpace C.left := hcompact
  let : Smooth C.hom := hsmooth
  let : LocallyOfFinitePresentation C.hom := hfp
  let V := flagVariety G
  let : CompactSpace V.scheme :=
    QuasiCompact.compactSpace_of_compactSpace V.toSpec
  let : IsAffineHom (pullback.diagonal (terminal.from V.scheme)) :=
    affine_variety_diagonal V
  let : LocallyOfFinitePresentation V.toSpec := inferInstance
  obtain ⟨T, Z, f, qF, hT, hn, hfpF, _hqcF, _hqsF, hF⟩ :=
    exists_finite_arithmetic_scheme V.toSpec
  let F : Over (Spec (.of T)) := Over.mk f
  let : AlgebraicGeometry.IsNoetherian F.left := hn
  let : CompactSpace F.left := inferInstance
  let : LocallyOfFinitePresentation F.hom := hfpF
  obtain ⟨r, _hr, hTR, rC, rF, hNC, hNF, hsm, hfpC, hfpF, hCartC, hCartF,
    _hOldC, _hOldF⟩ := @common_source_flag.{u} K inferInstance
      (pairedBSDHSource G a b) V.toOver S T hT C F
      inferInstance inferInstance inferInstance inferInstance inferInstance
      qC qF hC hF ⟨S, hS, le_rfl⟩
  exact ⟨r.val, stageScalarModel S C.hom r,
    stageScalarModel T F.hom ⟨r.val, r.property.1, hTR⟩,
    rC, rF, r.property.1, hNC, hNF, hsm, hfpC, hfpF, hCartC, hCartF⟩

end SchubertGeometry
