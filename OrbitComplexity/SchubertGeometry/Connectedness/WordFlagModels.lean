import OrbitComplexity.SchubertGeometry.Connectedness.WordTargetArrows
import OrbitComplexity.SchubertGeometry.Connectedness.DoubleScalarComparisons
import OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word endpoints and closed targets on one flag model

The proper word models, their endpoint maps and a finite family of closed
targets are retained over a common coefficient ring. The flag projection
to the prescribed model is Cartesian and preserves its comparison map.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private double_scalar_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.DoubleScalarComparisons
open private stage_map stage_map_cartesian stage_map_original scalar_fp scalar_qc scalar_property
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private inclusion_spec_comp
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
open private projection_chain
  from OrbitComplexity.SchubertGeometry.Connectedness.WordTargetArrows

private structure WordFlagModels
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {I : Type v}
    (G : ReductiveGroupData K) (words : I → List G.rootBase.support)
    (Y : I → Over (Spec (.of K))) (FK : Over (Spec (.of K)))
    (fK : ∀ i, Over.mk (bsdhToSpec G (words i)) ⟶ Y i)
    (jK : ∀ i, Y i ⟶ FK)
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S)))
    (qOriginal : FK.left ⟶ P.left) (start : CoefficientStage S) where
  stage : CoefficientStage S
  afterStart : start ≤ stage
  source : I → Over (Spec (.of stage.val))
  target : I → Over (Spec (.of stage.val))
  flag : Over (Spec (.of stage.val))
  endpoint : ∀ i, source i ⟶ target i
  inclusion : ∀ i, target i ⟶ flag
  sourceProper : ∀ i, IsProper (source i).hom
  sourceSmooth : ∀ i, Smooth (source i).hom
  endpointProper : ∀ i, IsProper (endpoint i).left
  targetFp : ∀ i, LocallyOfFinitePresentation (target i).hom
  inclusionClosed : ∀ i, IsClosedImmersion (inclusion i).left
  flagFp : LocallyOfFinitePresentation flag.hom
  flagQc : QuasiCompact flag.hom
  flagSeparated : IsSeparated flag.hom
  qSource : ∀ i, bsdhScheme G (words i) ⟶ (source i).left
  qTarget : ∀ i, (Y i).left ⟶ (target i).left
  qFlag : FK.left ⟶ flag.left
  sourceCartesian : ∀ i, IsPullback (qSource i) (bsdhToSpec G (words i)) (source i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap stage.val K)))
  targetCartesian : ∀ i, IsPullback (qTarget i) (Y i).hom (target i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap stage.val K)))
  flagCartesian : IsPullback qFlag FK.hom flag.hom
    (Spec.map (CommRingCat.ofHom (algebraMap stage.val K)))
  endpointSquare : ∀ i, qSource i ≫ (endpoint i).left = (fK i).left ≫ qTarget i
  inclusionSquare : ∀ i, qTarget i ≫ (inclusion i).left = (jK i).left ≫ qFlag
  flagProjection : flag.left ⟶ P.left
  projectionCartesian : IsPullback flagProjection flag.hom P.hom
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion stage.property.2).toRingHom))
  originalProjection : qFlag ≫ flagProjection = qOriginal

/-- Proper smooth word sources and their closed target inclusions are
retained over a common coefficient stage, preserving the Cartesian flag
projection and both endpoint and inclusion squares. -/
theorem exists_word_flag_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} [Finite I] (G : ReductiveGroupData K)
    (words : I → List G.rootBase.support)
    (Y : I → Over (Spec (.of K))) (FK : Over (Spec (.of K)))
    (fK : ∀ i, Over.mk (bsdhToSpec G (words i)) ⟶ Y i)
    (jK : ∀ i, Y i ⟶ FK)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (D : I → Over (Spec (.of S))) (P : Over (Spec (.of S)))
    [∀ i, LocallyOfFinitePresentation (D i).hom] [∀ i, IsSeparated (D i).hom]
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (j : ∀ i, D i ⟶ P) [∀ i, IsClosedImmersion (j i).left]
    (qD : ∀ i, (Y i).left ⟶ (D i).left) (qF : FK.left ⟶ P.left)
    (hD : ∀ i, IsPullback (qD i) (Y i).hom (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF FK.hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hj : ∀ i, qD i ≫ (j i).left = (jK i).left ≫ qF)
    (start : CoefficientStage S) :
    Nonempty (WordFlagModels G words Y FK fK jK S P qF start) := by
  obtain ⟨k, hk, A, l, f, mA, mD, h⟩ :=
    exists_word_target_arrows G words Y fK S hS D qD hD start
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : IsScalarTower S k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let : Algebra k.val l.val := (Subalgebra.inclusion l.property.2).toAlgebra
  let : IsScalarTower k.val l.val K :=
    Subalgebra.inclusion.isScalarTower_right l.property.2 K
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap l.val K))
  let P₁ := stageScalarModel S P.hom k
  let P₂ := stageScalarModel k.val P₁.hom l
  let qF₁ := stage_map S P FK qF hF k
  have hF₁ := stage_map_cartesian S P FK qF hF k
  let qF₂ := stage_map k.val P₁ FK qF₁ hF₁ l
  have hF₂ := stage_map_cartesian k.val P₁ FK qF₁ hF₁ l
  have hOld : qF₂ ≫ pullback.snd τ P₁.hom ≫ pullback.snd κ P.hom = qF :=
    projection_chain _ _ _ _ _
      (stage_map_original k.val P₁ FK qF₁ hF₁ l)
      (stage_map_original S P FK qF hF k)
  let T : CoefficientStage S :=
    ⟨l.val, l.property.1, k.property.2.trans l.property.2⟩
  let B : I → Over (Spec (.of l.val)) :=
    fun i => stageScalarModel k.val (stageScalarModel S (D i).hom k).hom l
  let j₂ : ∀ i, B i ⟶ P₂ :=
    fun i => chosenScalarArrow τ (chosenScalarArrow κ (j i))
  have hπ : IsPullback
      (pullback.snd τ P₁.hom ≫ pullback.snd κ P.hom) P₂.hom P.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion T.property.2).toRingHom)) := by
    have hp := (IsPullback.of_hasPullback τ P₁.hom).flip.paste_horiz
      (IsPullback.of_hasPullback κ P.hom).flip
    change IsPullback (pullback.snd τ P₁.hom ≫ pullback.snd κ P.hom)
      P₂.hom P.hom (τ ≫ κ) at hp
    simpa only [τ, κ, inclusion_spec_comp] using hp
  let : LocallyOfFinitePresentation P₁.hom := scalar_fp κ P
  let : QuasiCompact P₁.hom := scalar_qc κ P
  let : IsSeparated P₁.hom := by
    change IsSeparated (pullback.fst κ P.hom)
    infer_instance
  have hclosed : ∀ i, IsClosedImmersion (j₂ i).left := by
    intro i
    have h₁ := scalar_property (@IsClosedImmersion) κ (j i) inferInstance
    exact scalar_property (@IsClosedImmersion) τ (chosenScalarArrow κ (j i)) h₁
  have hfp : ∀ i, LocallyOfFinitePresentation (B i).hom := by
    intro i
    let D₁ := stageScalarModel S (D i).hom k
    let : LocallyOfFinitePresentation D₁.hom := scalar_fp κ (D i)
    exact scalar_fp τ D₁
  have htri : ∀ i, mD i ≫ (j₂ i).left = (jK i).left ≫ qF₂ := by
    intro i
    exact double_scalar_comparison κ τ ρ (j i) (jK i) (qD i) qF (mD i) qF₂
      (h i).2.2.2.2.1 hF₂ (h i).2.2.2.2.2.1 hOld (hj i)
  refine ⟨{
    stage := T
    afterStart := (show start.val ≤ k.val from hk).trans l.property.2
    source := fun i => stageScalarModel k.val (A i).hom l
    target := B
    flag := P₂
    endpoint := f
    inclusion := j₂
    sourceProper := fun i => (h i).1
    sourceSmooth := fun i => (h i).2.1
    endpointProper := fun i => (h i).2.2.1
    targetFp := hfp
    inclusionClosed := hclosed
    flagFp := scalar_fp τ P₁
    flagQc := scalar_qc τ P₁
    flagSeparated := ?_
    qSource := mA
    qTarget := mD
    qFlag := qF₂
    sourceCartesian := fun i => (h i).2.2.2.1
    targetCartesian := fun i => (h i).2.2.2.2.1
    flagCartesian := hF₂
    endpointSquare := fun i => (h i).2.2.2.2.2.2
    inclusionSquare := htri
    flagProjection := pullback.snd τ P₁.hom ≫ pullback.snd κ P.hom
    projectionCartesian := hπ
    originalProjection := hOld }⟩
  change IsSeparated (pullback.fst τ P₁.hom)
  infer_instance

end SchubertGeometry
