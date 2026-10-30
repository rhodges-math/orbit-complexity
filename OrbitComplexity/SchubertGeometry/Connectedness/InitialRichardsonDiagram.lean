import OrbitComplexity.SchubertGeometry.Connectedness.InitialFlagSource
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenTargetModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ArrowModels
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Initial arithmetic Richardson diagrams

The flag model gives a closed Richardson model. The smooth paired source
is extended to the same coefficient ring, and its endpoint descends between
these prescribed models.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

namespace SchubertGeometry

universe u

open private closed_target_stage
  from OrbitComplexity.SchubertGeometry.Connectedness.TargetStageObjects
open private scalar_closed
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private scalar_original
  from OrbitComplexity.FrobeniusSplitting.Normality.Models.ArrowModels

private def model_diagram {K : Type u} [CommRing K]
    (X Y Z : Over (Spec (.of K))) (g : X ⟶ Y) (j : Y ⟶ Z) : Prop :=
  ∃ (R : Subalgebra ℤ K) (C D F : Over (Spec (.of R)))
    (e : C ⟶ D) (r : D ⟶ F)
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left) (qF : Z.left ⟶ F.left),
    R.FG ∧ AlgebraicGeometry.IsNoetherian C.left ∧
    AlgebraicGeometry.IsNoetherian D.left ∧ AlgebraicGeometry.IsNoetherian F.left ∧
    Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
    LocallyOfFinitePresentation D.hom ∧ LocallyOfFinitePresentation F.hom ∧
    IsClosedImmersion r.left ∧
    IsPullback qC X.hom C.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    IsPullback qD Y.hom D.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    IsPullback qF Z.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    qC ≫ e.left = g.left ≫ qD ∧ qD ≫ r.left = j.left ≫ qF

private theorem scalar_triangle {B T N : Scheme.{u}}
    (κ : T ⟶ B) (ρ : N ⟶ T)
    (D F : Over B) (Y Z : Over N) (r : D ⟶ F) (j : Y ⟶ Z)
    (qD : Y.left ⟶ D.left) (qF : Z.left ⟶ F.left)
    (mD : Y.left ⟶ pullback κ D.hom) (mF : Z.left ⟶ pullback κ F.hom)
    (hD : mD ≫ pullback.fst κ D.hom = Y.hom ≫ ρ)
    (hF : mF ≫ pullback.fst κ F.hom = Z.hom ≫ ρ)
    (hpD : mD ≫ pullback.snd κ D.hom = qD)
    (hpF : mF ≫ pullback.snd κ F.hom = qF)
    (h : qD ≫ r.left = j.left ≫ qF) :
    mD ≫ (chosenScalarArrow κ r).left = j.left ≫ mF := by
  apply pullback.hom_ext
  · have ht : (chosenScalarArrow κ r).left ≫ pullback.fst κ F.hom =
        pullback.fst κ D.hom := (chosenScalarArrow κ r).w
    calc
      (mD ≫ (chosenScalarArrow κ r).left) ≫ pullback.fst κ F.hom =
          Y.hom ≫ ρ := by rw [Category.assoc, ht, hD]
      _ = (j.left ≫ mF) ≫ pullback.fst κ F.hom := by
        rw [Category.assoc, hF, ← Category.assoc, j.w]
  · calc
      (mD ≫ (chosenScalarArrow κ r).left) ≫ pullback.snd κ F.hom =
          qD ≫ r.left := by
        rw [Category.assoc, chosenScalarArrow_snd, ← Category.assoc, hpD]
      _ = j.left ≫ qF := h
      _ = (j.left ≫ mF) ≫ pullback.snd κ F.hom := by
        rw [Category.assoc, hpF]

private theorem endpoint_on_models
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    (C D F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [Smooth C.hom]
    [LocallyOfFinitePresentation C.hom]
    [CompactSpace D.left] [LocallyOfFinitePresentation D.hom]
    [CompactSpace F.left] [LocallyOfFinitePresentation F.hom]
    (X Y Z : Over (Spec (.of K))) (g : X ⟶ Y) (j : Y ⟶ Z)
    (r : D ⟶ F) [IsClosedImmersion r.left]
    (qC : X.left ⟶ C.left) (qD : Y.left ⟶ D.left) (qF : Z.left ⟶ F.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF Z.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hr : qD ≫ r.left = j.left ≫ qF) :
    model_diagram X Y Z g j := by
  obtain ⟨i, e, mC, mD, hCi, hDi, _hpC, hpD, he⟩ :=
    exists_arrow_model_stage S hS C D X Y g qC qD hC hD
  let κ := Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion i.property.2).toRingHom)
  let CR := stageScalarModel S C.hom i
  let DR := stageScalarModel S D.hom i
  let FR := stageScalarModel S F.hom i
  let (A : Over (Spec (.of S))) [CompactSpace A.left] :
      CompactSpace (stageScalarModel S A.hom i).left := by
    change CompactSpace ((modelScalarStages S A.hom).obj (op i))
    infer_instance
  let : Smooth CR.hom := by
    change Smooth (pullback.fst κ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation CR.hom := by
    change LocallyOfFinitePresentation (pullback.fst κ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation DR.hom := by
    change LocallyOfFinitePresentation (pullback.fst κ D.hom)
    infer_instance
  let : LocallyOfFinitePresentation FR.hom := by
    change LocallyOfFinitePresentation (pullback.fst κ F.hom)
    infer_instance
  let : Algebra.FiniteType ℤ i.val :=
    (Subalgebra.fg_iff_finiteType i.val).mp i.property.1
  have hnC := (finiteType_int_scheme_properties CR.hom).1
  have hnD := (finiteType_int_scheme_properties DR.hom).1
  have hnF := (finiteType_int_scheme_properties FR.hom).1
  let EF : Z ≅ genericScalarModel S F.hom := hF.flip.isoOverPullback
  let mF : Z.left ⟶ FR.left := EF.hom.left ≫ (modelScalarCone S F.hom).π.app (op i)
  have hFi := overIso_modelStage_cartesian S F.hom i Z EF
  have hpF : mF ≫ pullback.snd κ F.hom = qF :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => EF.hom.left ≫ k) (scalar_original S F.hom i)).trans
        hF.flip.isoOverPullback_hom_left_comp_snd)
  have hrR := scalar_triangle κ
    (Spec.map (CommRingCat.ofHom (algebraMap i.val K)))
    D F Y Z r j qD qF mD mF hDi.w hFi.w hpD hpF hr
  exact ⟨i.val, CR, DR, FR, e, chosenScalarArrow κ r, mC, mD, mF,
    i.property.1, hnC, hnD, hnF, inferInstance, inferInstance, inferInstance,
    inferInstance, scalar_closed κ r, hCi, hDi, hFi, he, hrR⟩

private theorem diagram_from_targets
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (C F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left] [Smooth C.hom]
    [LocallyOfFinitePresentation C.hom]
    [CompactSpace F.left] [LocallyOfFinitePresentation F.hom]
    (X Y Z : Over (Spec (.of K))) (g : X ⟶ Y) (j : Y ⟶ Z)
    (qC : X.left ⟶ C.left) (qF : Z.left ⟶ F.left)
    (hC : IsPullback qC X.hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S)
    (hdata : closed_target_stage S Z (fun _ : PUnit.{u+1} => Y)
      (fun _ => j) F qF start) :
    model_diagram X Y Z g j := by
  obtain ⟨k, _hk, D, r, mF, mD, hFk, _hpF, htargets⟩ := hdata
  obtain ⟨hr, hDk, hj, hfpD, hcompactD, _hqsD⟩ := htargets PUnit.unit
  let Ck := stageScalarModel S C.hom k
  let Fk := stageScalarModel S F.hom k
  let EC : X ≅ genericScalarModel S C.hom := hC.flip.isoOverPullback
  let mC : X.left ⟶ Ck.left :=
    EC.hom.left ≫ (modelScalarCone S C.hom).π.app (op k)
  have hCk := overIso_modelStage_cartesian S C.hom k X EC
  let : CompactSpace Ck.left := by
    change CompactSpace ((modelScalarStages S C.hom).obj (op k))
    infer_instance
  let : QuasiSeparatedSpace Ck.left := by
    change QuasiSeparatedSpace ((modelScalarStages S C.hom).obj (op k))
    infer_instance
  let : Smooth Ck.hom := by
    change Smooth (pullback.fst _ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation Ck.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ C.hom)
    infer_instance
  let : CompactSpace Fk.left := by
    change CompactSpace ((modelScalarStages S F.hom).obj (op k))
    infer_instance
  let : LocallyOfFinitePresentation Fk.hom := by
    change LocallyOfFinitePresentation (pullback.fst _ F.hom)
    infer_instance
  let : CompactSpace (D PUnit.unit).left := hcompactD
  let : LocallyOfFinitePresentation (D PUnit.unit).hom := hfpD
  let : IsClosedImmersion (r PUnit.unit).left := hr
  exact endpoint_on_models k.val k.property.1 Ck (D PUnit.unit) Fk X Y Z g j
    (r PUnit.unit) mC (mD PUnit.unit) mF hCk hDk hFk hj

/-- Two reduced words give an arithmetic paired endpoint to a closed
Richardson model inside a flag model, retaining all three Cartesian
comparisons and both endpoint triangles. The source model is smooth. -/
theorem exists_initial_richardson_diagram
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    model_diagram (pairedBSDHSource G a b)
      (richardsonVariety G
        (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
        (ReductiveGroups.simpleWeylWord G.rootBase a)).toOver
      (flagVariety G).toOver (pairedRichardsonMap G a b ha hb)
      (richardsonInclusion G
        (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
        (ReductiveGroups.simpleWeylWord G.rootBase a)) := by
  obtain ⟨S, C, F, qC, qF, hS, hnC, hnF, hsmooth, hfpC, hfpF, hC, hF⟩ :=
    exists_initial_flag_source G a b ha hb
  let : AlgebraicGeometry.IsNoetherian C.left := hnC
  let : AlgebraicGeometry.IsNoetherian F.left := hnF
  let : CompactSpace C.left := inferInstance
  let : QuasiSeparatedSpace C.left := inferInstance
  let : CompactSpace F.left := inferInstance
  let : Smooth C.hom := hsmooth
  let : LocallyOfFinitePresentation C.hom := hfpC
  let : LocallyOfFinitePresentation F.hom := hfpF
  let V := flagVariety G
  let : CompactSpace V.scheme :=
    QuasiCompact.compactSpace_of_compactSpace V.toSpec
  obtain ⟨I, finiteI, U, hU, hcover⟩ := exists_finite_affine_opens V.scheme
  let : Finite I := finiteI
  let v := G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b
  let w := ReductiveGroups.simpleWeylWord G.rootBase a
  let Z : PUnit.{u+1} → TopologicalSpace.Closeds V.scheme :=
    fun _ => richardsonSupport G v w
  let start : CoefficientStage S := ⟨S, hS, le_rfl⟩
  have htargets := exists_chosen_closed_targets G Z U hU hcover S hS F qF hF start
  exact diagram_from_targets S C F (pairedBSDHSource G a b)
    (richardsonVariety G v w).toOver V.toOver (pairedRichardsonMap G a b ha hb)
    (richardsonInclusion G v w) qC qF hC start htargets

end SchubertGeometry
