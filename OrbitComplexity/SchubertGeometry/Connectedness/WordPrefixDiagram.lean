import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointDiagram
import Mathlib.GroupTheory.Coxeter.Length
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Arithmetic endpoint diagrams for strict word prefixes

Finite affine opens and the coordinate Schubert target construction provide
the strict-prefix targets. Their endpoint diagrams share a scalar extension
of the prescribed flag model and retain its original comparison. The final
word source and endpoint are not selected by this construction.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private common_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
open private coefficient_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private target_result
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private scalar_functor
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private tensor_functor tensor_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private variety_diagonal
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

private structure TargetModels {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S))) (start : CoefficientStage S)
    {I : Type u} (Z : I → Over (Spec (.of K))) (FK : Over (Spec (.of K)))
    (jK : ∀ i, Z i ⟶ FK) (qOriginal : FK.left ⟶ P.left) where
  coefficient : Subalgebra ℤ K
  finiteGeneration : coefficient.FG
  original_le : S ≤ coefficient
  start_le : start.val ≤ coefficient
  flag : Over (Spec (.of coefficient))
  projection : flag.left ⟶ P.left
  flagComparison : FK.left ⟶ flag.left
  target : I → Over (Spec (.of coefficient))
  inclusion : ∀ i, target i ⟶ flag
  targetComparison : ∀ i, (Z i).left ⟶ (target i).left
  projection_square : IsPullback projection flag.hom P.hom
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion original_le).toRingHom))
  flag_square : IsPullback flagComparison FK.hom flag.hom
    (Spec.map (CommRingCat.ofHom (algebraMap coefficient K)))
  flag_original : flagComparison ≫ projection = qOriginal
  flag_presentation : LocallyOfFinitePresentation flag.hom
  flag_compact : QuasiCompact flag.hom
  flag_separated : IsSeparated flag.hom
  target_presentation : ∀ i, LocallyOfFinitePresentation (target i).hom
  target_compact : ∀ i, QuasiCompact (target i).hom
  target_separated : ∀ i, IsSeparated (target i).hom
  inclusion_closed : ∀ i, IsClosedImmersion (inclusion i).left
  target_square : ∀ i, IsPullback (targetComparison i) (Z i).hom (target i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap coefficient K)))
  inclusion_comparison : ∀ i, targetComparison i ≫ (inclusion i).left =
    (jK i).left ≫ flagComparison

private structure PrefixEndpointData {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} (G : ReductiveGroupData K) (words : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (words i))
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S))) (start : CoefficientStage S)
    (qOriginal : (flagVariety G).scheme ⟶ P.left) where
  coefficient : Subalgebra ℤ K
  finiteGeneration : coefficient.FG
  original_le : S ≤ coefficient
  start_le : start.val ≤ coefficient
  flag : Over (Spec (.of coefficient))
  projection : flag.left ⟶ P.left
  flagComparison : (flagVariety G).scheme ⟶ flag.left
  source : I → Over (Spec (.of coefficient))
  target : I → Over (Spec (.of coefficient))
  endpoint : ∀ i, source i ⟶ target i
  inclusion : ∀ i, target i ⟶ flag
  sourceComparison : ∀ i, bsdhScheme G (words i) ⟶ (source i).left
  targetComparison : ∀ i,
    (schubertVariety G (simpleWeylWord G.rootBase (words i))).scheme ⟶ (target i).left
  projection_square : IsPullback projection flag.hom P.hom
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion original_le).toRingHom))
  flag_square : IsPullback flagComparison (flagVariety G).toSpec flag.hom
    (Spec.map (CommRingCat.ofHom (algebraMap coefficient K)))
  flag_original : flagComparison ≫ projection = qOriginal
  flag_presentation : LocallyOfFinitePresentation flag.hom
  flag_compact : QuasiCompact flag.hom
  flag_separated : IsSeparated flag.hom
  source_presentation : ∀ i, LocallyOfFinitePresentation (source i).hom
  source_compact : ∀ i, QuasiCompact (source i).hom
  target_presentation : ∀ i, LocallyOfFinitePresentation (target i).hom
  target_compact : ∀ i, QuasiCompact (target i).hom
  target_separated : ∀ i, IsSeparated (target i).hom
  endpoint_proper : ∀ i, IsProper (endpoint i).left
  inclusion_closed : ∀ i, IsClosedImmersion (inclusion i).left
  source_square : ∀ i, IsPullback (sourceComparison i) (bsdhToSpec G (words i))
    (source i).hom (Spec.map (CommRingCat.ofHom (algebraMap coefficient K)))
  target_square : ∀ i, IsPullback (targetComparison i)
    (schubertVariety G (simpleWeylWord G.rootBase (words i))).toSpec (target i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap coefficient K)))
  endpoint_comparison : ∀ i, sourceComparison i ≫ (endpoint i).left =
    (bsdhSchubertMap G (words i) (hred i)).left ≫ targetComparison i
  inclusion_comparison : ∀ i, targetComparison i ≫ (inclusion i).left =
    (schubertInclusion G (simpleWeylWord G.rootBase (words i))).left ≫ flagComparison

private theorem over_base_pullback {B T : Scheme.{u}} {X Y : Over B}
    (j : X ⟶ Y) {Z : Scheme.{u}} (q : X.left ⟶ Z) (z : Z ⟶ T) (κ : B ⟶ T)
    (h : IsPullback q (j.left ≫ Y.hom) z κ) : IsPullback q X.hom z κ := by
  have hj : j.left ≫ Y.hom = X.hom := j.w
  exact hj ▸ h

private theorem reindex_prefix_models {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] {I : Type u} {J : Type v}
    (G : ReductiveGroupData K) (words : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (words i))
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S))) (start : CoefficientStage S)
    (q : (flagVariety G).scheme ⟶ P.left)
    (d : PrefixEndpointData G words hred S P start q) (f : J → I) :
    Nonempty (PrefixEndpointData G (fun j => words (f j))
      (fun j => hred (f j)) S P start q) :=
  ⟨{
    coefficient := d.coefficient
    finiteGeneration := d.finiteGeneration
    original_le := d.original_le
    start_le := d.start_le
    flag := d.flag
    projection := d.projection
    flagComparison := d.flagComparison
    source := fun j => d.source (f j)
    target := fun j => d.target (f j)
    endpoint := fun j => d.endpoint (f j)
    inclusion := fun j => d.inclusion (f j)
    sourceComparison := fun j => d.sourceComparison (f j)
    targetComparison := fun j => d.targetComparison (f j)
    projection_square := d.projection_square
    flag_square := d.flag_square
    flag_original := d.flag_original
    flag_presentation := d.flag_presentation
    flag_compact := d.flag_compact
    flag_separated := d.flag_separated
    source_presentation := fun j => d.source_presentation (f j)
    source_compact := fun j => d.source_compact (f j)
    target_presentation := fun j => d.target_presentation (f j)
    target_compact := fun j => d.target_compact (f j)
    target_separated := fun j => d.target_separated (f j)
    endpoint_proper := fun j => d.endpoint_proper (f j)
    inclusion_closed := fun j => d.inclusion_closed (f j)
    source_square := fun j => d.source_square (f j)
    target_square := fun j => d.target_square (f j)
    endpoint_comparison := fun j => d.endpoint_comparison (f j)
    inclusion_comparison := fun j => d.inclusion_comparison (f j)
  }⟩

private theorem inclusion_spec_comp {K : Type u} [CommRing K]
    {S T R : Subalgebra ℤ K} (hST : S ≤ T) (hTR : T ≤ R) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTR).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hST.trans hTR)).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

private theorem triple_projection {C : Type v} [Category C]
    {A B D E X : C} (q : X ⟶ A) (p : A ⟶ B) (r : B ⟶ D) (s : D ⟶ E)
    (q₁ : X ⟶ B) (q₂ : X ⟶ D) (q₃ : X ⟶ E)
    (h₁ : q ≫ p = q₁) (h₂ : q₁ ≫ r = q₂) (h₃ : q₂ ≫ s = q₃) :
    q ≫ (p ≫ r ≫ s) = q₃ := by
  rw [← Category.assoc, h₁, ← Category.assoc, h₂, h₃]

private theorem nested_projection_square {B T U : Scheme.{u}}
    (κ : T ⟶ B) (τ : U ⟶ T) (P : Over B) :
    IsPullback (pullback.snd τ (pullback.fst κ P.hom) ≫ pullback.snd κ P.hom)
      (pullback.fst τ (pullback.fst κ P.hom)) P.hom (τ ≫ κ) :=
  ((IsPullback.of_hasPullback τ (pullback.fst κ P.hom)).flip).paste_horiz
    (IsPullback.of_hasPullback κ P.hom).flip

private theorem common_target_models {K I J : Type u} [CommRing K]
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (start : CoefficientStage S₀) (Z : I → Over (Spec (.of K)))
    (FK : Over (Spec (.of K))) (jK : ∀ i, Z i ⟶ FK)
    [IsAffineHom (pullback.diagonal (terminal.from FK.left))]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (Z i).left))]
    [∀ i, IsClosedImmersion (jK i).left]
    (U : J → FK.left.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (qOriginal : FK.left ⟶ P.left)
    (h : common_targets (fun i => (Z i).left) (fun i => (jK i).left)
      FK.hom U hU S₀ P qOriginal start) :
    Nonempty (TargetModels S₀ P start Z FK jK qOriginal) := by
  classical
  rcases h with ⟨S, N, e, β, T, h₀, hST, hstart, hT, h⟩
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : Algebra S₀ T := (Subalgebra.inclusion h₀).toAlgebra
  let : IsScalarTower S₀ T K := Subalgebra.inclusion.isScalarTower_right h₀ K
  rcases h with ⟨qT, _hqT, _hqTf, hqTs, _he, ⟨k, hk⟩, _hflat⟩
  rcases hk with ⟨qPk, hPk, _hnF, _hnB, _hPkf, hPks, _heₖ, hr, _hflatₖ⟩
  rcases hr with ⟨cFM, cBM, qFM, qBM, jM, _hcFM, _hcBM, _hclosed,
    _hqFM, _hqBM, _hfnode, _hbnode, _hjnode, _hjfield,
    l, _hl, E, _hEk, hqR, hqRs, hD⟩
  let κ₀ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h₀).toRingHom)
  let κ₁ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let κ₂ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let PT : Over (Spec (.of T)) := (scalar_functor κ₀).obj P
  let Pk : Over (Spec (.of k.val)) := stageScalarModel T PT.hom k
  let PR : Over (Spec (.of l.val)) := stageScalarModel k.val Pk.hom l
  let qR : FK.left ⟶ PR.left :=
    (hPk.flip.isoOverPullback).hom.left ≫ (modelScalarCone k.val Pk.hom).π.app (op l)
  let π : PR.left ⟶ P.left :=
    pullback.snd κ₂ Pk.hom ≫ pullback.snd κ₁ PT.hom ≫ pullback.snd κ₀ P.hom
  let DR (i : I) : Over (Spec (.of l.val)) := stageScalarModel k.val (cBM i).pt.hom l
  let jR (i : I) : DR i ⟶ PR := chosenScalarArrow κ₂ (jM i) ≫ E.hom
  choose qDR hjR hqDR hjDR _hqDRs hfpD _hcD _hqsD using hD
  have hbase : κ₂ ≫ κ₁ ≫ κ₀ =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (h₀.trans (k.property.2.trans l.property.2))).toRingHom) := by
    calc
      κ₂ ≫ κ₁ ≫ κ₀ = (κ₂ ≫ κ₁) ≫ κ₀ := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (k.property.2.trans l.property.2)).toRingHom) ≫ κ₀ :=
        congrArg (fun z => z ≫ κ₀) (inclusion_spec_comp k.property.2 l.property.2)
      _ = _ := inclusion_spec_comp h₀ (k.property.2.trans l.property.2)
  have hπ : IsPullback π PR.hom P.hom
      (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (h₀.trans (k.property.2.trans l.property.2))).toRingHom)) := by
    have h₁ := (IsPullback.of_hasPullback κ₀ P.hom).flip
    have h₂ := (IsPullback.of_hasPullback κ₁ PT.hom).flip
    have h₃ := (IsPullback.of_hasPullback κ₂ Pk.hom).flip
    change IsPullback (pullback.snd κ₂ Pk.hom ≫ pullback.snd κ₁ PT.hom ≫
      pullback.snd κ₀ P.hom) (pullback.fst κ₂ Pk.hom) P.hom _
    have hp : IsPullback (pullback.snd κ₂ Pk.hom ≫ pullback.snd κ₁ PT.hom ≫
        pullback.snd κ₀ P.hom) (pullback.fst κ₂ Pk.hom) P.hom
        (κ₂ ≫ κ₁ ≫ κ₀) := h₃.paste_horiz (h₂.paste_horiz h₁)
    exact hbase ▸ hp
  have hpF : LocallyOfFinitePresentation PR.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hπ inferInstance
  have hqcF : QuasiCompact PR.hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hπ inferInstance
  have hsF : IsSeparated PR.hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hπ inferInstance
  let : QuasiCompact PR.hom := hqcF
  let : IsSeparated PR.hom := hsF
  have hqcD (i : I) : QuasiCompact (DR i).hom := by
    let : IsClosedImmersion (jR i).left := hjR i
    have hc : QuasiCompact ((jR i).left ≫ PR.hom) := inferInstance
    exact (jR i).w ▸ hc
  have hsD (i : I) : IsSeparated (DR i).hom := by
    let : IsClosedImmersion (jR i).left := hjR i
    have hs : IsSeparated ((jR i).left ≫ PR.hom) := inferInstance
    exact (jR i).w ▸ hs
  have hfield (i : I) : IsPullback (qDR i) (Z i).hom (DR i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) := by
    have hi := hqDR i
    change IsPullback (qDR i) ((jK i).left ≫ FK.hom) (DR i).hom _ at hi
    exact over_base_pullback (jK i) (qDR i) (DR i).hom _ hi
  exact ⟨{
    coefficient := l.val
    finiteGeneration := l.property.1
    original_le := h₀.trans (k.property.2.trans l.property.2)
    start_le := hstart.trans (k.property.2.trans l.property.2)
    flag := PR
    projection := π
    flagComparison := qR
    target := DR
    inclusion := jR
    targetComparison := qDR
    projection_square := hπ
    flag_square := hqR
    flag_original := triple_projection qR _ _ _ qPk qT qOriginal hqRs hPks hqTs
    flag_presentation := hpF
    flag_compact := hqcF
    flag_separated := hsF
    target_presentation := hfpD
    target_compact := hqcD
    target_separated := hsD
    inclusion_closed := hjR
    target_square := hfield
    inclusion_comparison := hjDR
  }⟩

private theorem add_word_endpoints {K I : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] [Finite I]
    (G : ReductiveGroupData K) (words : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (words i))
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S))) (start : CoefficientStage S)
    (qOriginal : (flagVariety G).scheme ⟶ P.left)
    (data : TargetModels S P start
      (fun i => (schubertVariety G (simpleWeylWord G.rootBase (words i))).toOver)
      (flagVariety G).toOver
      (fun i => schubertInclusion G (simpleWeylWord G.rootBase (words i))) qOriginal) :
    Nonempty (PrefixEndpointData G words hred S P start qOriginal) := by
  classical
  rcases data with ⟨R, hR, hSR, hstart, F, πF, qF, D, j, qD, hπF, hF,
    hFOriginal, hfpF, hqcF, hsF, hfpD, hqcD, hsD, hj, hD, hDj⟩
  let : ∀ i, LocallyOfFinitePresentation (D i).hom := hfpD
  let : ∀ i, IsSeparated (D i).hom := hsD
  let : ∀ i, IsClosedImmersion (j i).left := hj
  obtain ⟨k, _hk, A, qA, l, f, mA, mD, mF, hmF, hmFOld, h⟩ :=
    exists_word_endpoint_diagram G words hred R hR ⟨R, hR, le_rfl⟩ D F j qD qF hD hF hDj
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let FR := stageScalarModel k.val (stageScalarModel R F.hom k).hom l
  let AR (i : I) := stageScalarModel k.val (A i).hom l
  let DR (i : I) := stageScalarModel k.val (stageScalarModel R (D i).hom k).hom l
  let jR (i : I) := chosenScalarArrow τ (chosenScalarArrow κ (j i))
  let πR : FR.left ⟶ P.left :=
    (pullback.snd τ (stageScalarModel R F.hom k).hom ≫ pullback.snd κ F.hom) ≫ πF
  have hbase : (τ ≫ κ) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (hSR.trans (k.property.2.trans l.property.2))).toRingHom) := by
    rw [inclusion_spec_comp k.property.2 l.property.2]
    exact inclusion_spec_comp hSR (k.property.2.trans l.property.2)
  have hπR : IsPullback πR FR.hom P.hom
      (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (hSR.trans (k.property.2.trans l.property.2))).toRingHom)) := by
    have hs := (nested_projection_square κ τ F).paste_horiz hπF
    change IsPullback ((pullback.snd τ (pullback.fst κ F.hom) ≫
      pullback.snd κ F.hom) ≫ πF) (pullback.fst τ (pullback.fst κ F.hom)) P.hom _
    exact hbase ▸ hs
  have hNested := nested_projection_square κ τ F
  have hpFR : LocallyOfFinitePresentation FR.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hNested hfpF
  have hqcFR : QuasiCompact FR.hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hNested hqcF
  have hsFR : IsSeparated FR.hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hNested hsF
  have hOriginal : mF ≫ πR = qOriginal := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ πF) hmFOld).trans hFOriginal)
  have hpAR (i : I) : LocallyOfFinitePresentation (AR i).hom := by
    let : Smooth (A i).hom := (h i).1.2.1
    change LocallyOfFinitePresentation (pullback.fst τ (A i).hom)
    infer_instance
  have hqcAR (i : I) : QuasiCompact (AR i).hom := by
    let : IsProper (A i).hom := (h i).1.1
    change QuasiCompact (pullback.fst τ (A i).hom)
    infer_instance
  let : ∀ i, QuasiCompact (D i).hom := hqcD
  let : ∀ i, LocallyOfFinitePresentation (D i).hom := hfpD
  let : ∀ i, IsSeparated (D i).hom := hsD
  exact ⟨{
    coefficient := l.val
    finiteGeneration := l.property.1
    original_le := hSR.trans (k.property.2.trans l.property.2)
    start_le := hstart.trans (k.property.2.trans l.property.2)
    flag := FR
    projection := πR
    flagComparison := mF
    source := AR
    target := DR
    endpoint := f
    inclusion := jR
    sourceComparison := mA
    targetComparison := mD
    projection_square := hπR
    flag_square := hmF
    flag_original := hOriginal
    flag_presentation := hpFR
    flag_compact := hqcFR
    flag_separated := hsFR
    source_presentation := hpAR
    source_compact := hqcAR
    target_presentation := fun i => MorphismProperty.of_isPullback
      (P := @LocallyOfFinitePresentation) (nested_projection_square κ τ (D i)) (hfpD i)
    target_compact := fun i => MorphismProperty.of_isPullback
      (P := @QuasiCompact) (nested_projection_square κ τ (D i)) (hqcD i)
    target_separated := fun i => MorphismProperty.of_isPullback
      (P := @IsSeparated) (nested_projection_square κ τ (D i)) (hsD i)
    endpoint_proper := fun i => (h i).1.2.2.2.2.2.2.2.2.2.2
    inclusion_closed := fun i => (h i).2.1
    source_square := fun i => (h i).1.2.2.2.2.1
    target_square := fun i => (h i).1.2.2.2.2.2.1
    endpoint_comparison := fun i => (h i).1.2.2.2.2.2.2.2.2.1
    inclusion_comparison := fun i => (h i).2.2
  }⟩

private theorem finite_affine_opens (X : Scheme.{u}) [CompactSpace X] :
    ∃ (J : Type u) (_ : Fintype J) (U : J → X.Opens),
      (∀ j, IsAffineOpen (U j)) ∧ (⨆ j, U j) = ⊤ := by
  let C := X.affineCover.finiteSubcover
  exact ⟨C.I₀, inferInstance, (fun j => (C.f j).opensRange),
    (fun j => isAffineOpen_opensRange (C.f j)), C.iSup_opensRange⟩

/-- The strict prefixes of a reduced word have arithmetic endpoint diagrams
over a common coefficient extension of the prescribed flag model. A finite
affine cover, closed Schubert targets, and endpoint source models are all
constructed internally; the final word endpoint is outside this family. -/
theorem exists_word_prefix_diagram {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S) :
    Nonempty (PrefixEndpointData G (fun p : Fin word.length => word.take p.val)
      (fun p : Fin word.length => hred.take p.val) S P start qF) := by
  classical
  let : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  obtain ⟨J, hJ, U, hU, hcover⟩ := finite_affine_opens (flagVariety G).scheme
  let : Fintype J := hJ
  let words : ULift.{u} (Fin word.length) → List G.rootBase.support :=
    fun p => word.take p.down.val
  let w : ULift.{u} (Fin word.length) → G.weylGroup := fun p => simpleWeylWord G.rootBase (words p)
  let Z := fun p : ULift.{u} (Fin word.length) => (schubertVariety G (w p)).toOver
  let jK := fun p : ULift.{u} (Fin word.length) => schubertInclusion G (w p)
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).toOver.left)) :=
    variety_diagonal (flagVariety G)
  let : ∀ p : ULift.{u} (Fin word.length), IsAffineHom (pullback.diagonal (terminal.from (Z
    p).left)) :=
    fun p => variety_diagonal (schubertVariety G (w p))
  obtain ⟨data⟩ := common_target_models S P start Z (flagVariety G).toOver jK U hU qF
    (exists_prefix_common_coefficients G w U hU hcover S hS P qF hF start)
  obtain ⟨d⟩ := add_word_endpoints G words
    (fun p : ULift.{u} (Fin word.length) => hred.take p.down.val) S P start qF data
  exact reindex_prefix_models G words
    (fun p : ULift.{u} (Fin word.length) => hred.take p.down.val)
    S P start qF d (fun p : Fin word.length => ULift.up p)

end SchubertGeometry
