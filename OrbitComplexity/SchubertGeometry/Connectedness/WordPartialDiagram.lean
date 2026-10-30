import OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
import OrbitComplexity.SchubertGeometry.Connectedness.WordPartialFlags
import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointTriangles
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Shared endpoint and partial-flag diagrams

The strict-prefix endpoint models and a given final endpoint are placed over
one flag model. Complete-to-partial projections and two scalar extensions then
preserve the endpoint triangles and their original-model projections.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private PrefixEndpointData
  PrefixEndpointData.coefficient
  PrefixEndpointData.finiteGeneration
  PrefixEndpointData.original_le
  PrefixEndpointData.start_le
  PrefixEndpointData.flag
  PrefixEndpointData.projection
  PrefixEndpointData.flagComparison
  PrefixEndpointData.source
  PrefixEndpointData.target
  PrefixEndpointData.endpoint
  PrefixEndpointData.inclusion
  PrefixEndpointData.sourceComparison
  PrefixEndpointData.targetComparison
  PrefixEndpointData.projection_square
  PrefixEndpointData.flag_square
  PrefixEndpointData.flag_original
  PrefixEndpointData.flag_presentation
  PrefixEndpointData.flag_compact
  PrefixEndpointData.flag_separated
  PrefixEndpointData.source_presentation
  PrefixEndpointData.source_compact
  PrefixEndpointData.target_presentation
  PrefixEndpointData.target_compact
  PrefixEndpointData.target_separated
  PrefixEndpointData.endpoint_proper
  PrefixEndpointData.inclusion_closed
  PrefixEndpointData.source_square
  PrefixEndpointData.target_square
  PrefixEndpointData.endpoint_comparison
  PrefixEndpointData.inclusion_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPrefixDiagram
open private coefficient_triangle source_scalar_square
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels
open private scalar_triangle scalarArrow_isPullback
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointTriangles
open private inner_projection_base
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointDiagram

private def ScalarFamilyFacts {B BK T : Scheme.{u}} {I : Type v}
    (κ : T ⟶ B) (ρ : BK ⟶ T)
    (A D : I → Over B) (F : Over B)
    (AK DK : I → Over BK) (FK : Over BK)
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ FK)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left)
    (qAT : ∀ i, (AK i).left ⟶ pullback κ (A i).hom)
    (qDT : ∀ i, (DK i).left ⟶ pullback κ (D i).hom)
    (qFT : FK.left ⟶ pullback κ F.hom) : Prop :=
  IsPullback qFT FK.hom (pullback.fst κ F.hom) ρ ∧
  ∀ i, qAT i ≫ pullback.fst κ (A i).hom = (AK i).hom ≫ ρ ∧
    qAT i ≫ pullback.snd κ (A i).hom = qA i ∧
    IsPullback (qAT i) (AK i).hom (pullback.fst κ (A i).hom) ρ ∧
    qDT i ≫ pullback.fst κ (D i).hom = (DK i).hom ≫ ρ ∧
    qDT i ≫ pullback.snd κ (D i).hom = qD i ∧
    IsPullback (qDT i) (DK i).hom (pullback.fst κ (D i).hom) ρ ∧
    qAT i ≫ (chosenScalarArrow κ (e i)).left = (eK i).left ≫ qDT i ∧
    qDT i ≫ (chosenScalarArrow κ (j i)).left = (jK i).left ≫ qFT ∧
    IsProper (chosenScalarArrow κ (e i)).left ∧
    IsClosedImmersion (chosenScalarArrow κ (j i)).left

private def DoubleFamilyFacts {B T U BK : Scheme.{u}} {I : Type v}
    (κ : T ⟶ B) (τ : U ⟶ T) (ρ : BK ⟶ U) (σ : BK ⟶ T)
    (A D : I → Over B) (F : Over B)
    (AK DK : I → Over BK) (FK : Over BK)
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ FK)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left)
    (mF : FK.left ⟶ pullback τ (pullback.fst κ F.hom)) : Prop :=
  let A₁ : I → Over T := fun i => Over.mk (pullback.fst κ (A i).hom)
  let D₁ : I → Over T := fun i => Over.mk (pullback.fst κ (D i).hom)
  let F₁ : Over T := Over.mk (pullback.fst κ F.hom)
  let qF₁ := mF ≫ pullback.snd τ F₁.hom
  ∃ (qA₁ : ∀ i, (AK i).left ⟶ (A₁ i).left)
    (qD₁ : ∀ i, (DK i).left ⟶ (D₁ i).left)
    (qA₂ : ∀ i, (AK i).left ⟶ pullback τ (A₁ i).hom)
    (qD₂ : ∀ i, (DK i).left ⟶ pullback τ (D₁ i).hom),
    ScalarFamilyFacts κ σ A D F AK DK FK e j eK jK qA qD qA₁ qD₁ qF₁ ∧
    ScalarFamilyFacts τ ρ A₁ D₁ F₁ AK DK FK
      (fun i => chosenScalarArrow κ (e i)) (fun i => chosenScalarArrow κ (j i))
      eK jK qA₁ qD₁ qA₂ qD₂ mF

private theorem double_endpoint_family {B T U BK : Scheme.{u}} {I : Type v}
    (κ : T ⟶ B) (τ : U ⟶ T) (ρ : BK ⟶ U) (σ : BK ⟶ T) (η : BK ⟶ B)
    (hρ : ρ ≫ τ = σ) (hσ : σ ≫ κ = η)
    (A D : I → Over B) (F : Over B)
    (AK DK : I → Over BK) (FK : Over BK)
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    [∀ i, IsProper (e i).left] [∀ i, IsClosedImmersion (j i).left]
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ FK)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left) (qF : FK.left ⟶ F.left)
    (hA : ∀ i, IsPullback (qA i) (AK i).hom (A i).hom η)
    (hD : ∀ i, IsPullback (qD i) (DK i).hom (D i).hom η)
    (hF : IsPullback qF FK.hom F.hom η)
    (he : ∀ i, qA i ≫ (e i).left = (eK i).left ≫ qD i)
    (hj : ∀ i, qD i ≫ (j i).left = (jK i).left ≫ qF)
    (mF : FK.left ⟶ pullback τ (pullback.fst κ F.hom))
    (hFf : mF ≫ pullback.fst τ (pullback.fst κ F.hom) = FK.hom ≫ ρ)
    (hFs : mF ≫ pullback.snd τ (pullback.fst κ F.hom) ≫
      pullback.snd κ F.hom = qF) :
    DoubleFamilyFacts κ τ ρ σ A D F AK DK FK e j eK jK qA qD mF := by
  let A₁ : I → Over T := fun i => Over.mk (pullback.fst κ (A i).hom)
  let D₁ : I → Over T := fun i => Over.mk (pullback.fst κ (D i).hom)
  let F₁ : Over T := Over.mk (pullback.fst κ F.hom)
  let qF₁ := mF ≫ pullback.snd τ F₁.hom
  have hF₁f : qF₁ ≫ F₁.hom = FK.hom ≫ σ := by
    exact (inner_projection_base τ ρ F₁.hom FK.hom mF hFf).trans
      (congrArg (fun z => FK.hom ≫ z) hρ)
  obtain ⟨qA₁, qD₁, hF₁, h₁⟩ := scalar_endpoint_triangles κ σ η hσ
    A D F AK DK FK e j eK jK qA qD qF hA hD hF he hj qF₁ hF₁f hFs
  let : ∀ i, IsProper (chosenScalarArrow κ (e i)).left := fun i => by
    rcases h₁ i with ⟨_, _, _, _, _, _, _, _, hp, _⟩
    exact hp
  let : ∀ i, IsClosedImmersion (chosenScalarArrow κ (j i)).left := fun i => by
    rcases h₁ i with ⟨_, _, _, _, _, _, _, _, _, hc⟩
    exact hc
  obtain ⟨qA₂, qD₂, hF₂, h₂⟩ := scalar_endpoint_triangles τ ρ σ hρ
    A₁ D₁ F₁ AK DK FK
    (fun i => chosenScalarArrow κ (e i)) (fun i => chosenScalarArrow κ (j i))
    eK jK qA₁ qD₁ qF₁
    (fun i => (h₁ i).2.2.1) (fun i => (h₁ i).2.2.2.2.2.1) hF₁
    (fun i => (h₁ i).2.2.2.2.2.2.1)
    (fun i => (h₁ i).2.2.2.2.2.2.2.1) mF hFf rfl
  exact ⟨qA₁, qD₁, qA₂, qD₂, ⟨hF₁, h₁⟩, ⟨hF₂, h₂⟩⟩

private def scalarFlagInclusion {B T : Scheme.{u}} (κ : T ⟶ B)
    (D P : Over B) (j : D ⟶ P) (F : Over T) (π : F.left ⟶ P.left)
    (hπ : IsPullback π F.hom P.hom κ) :
    Over.mk (pullback.fst κ D.hom) ⟶ F :=
  chosenScalarArrow κ j ≫ hπ.flip.isoOverPullback.inv

private theorem triangle_cancel {C : Type v} [Category C]
    {A B D E F : C} (q : A ⟶ B) (j : B ⟶ D)
    (a : A ⟶ E) (b : E ⟶ F) (i : F ⟶ D) (r : D ⟶ F)
    (hir : i ≫ r = 𝟙 F) (h : q ≫ j = a ≫ b ≫ i) :
    q ≫ (j ≫ r) = a ≫ b := by
  rw [← Category.assoc, h, Category.assoc, Category.assoc, hir, Category.comp_id]

private def FinalScalarFacts {B BK T : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T)
    (C D P : Over B) (e : C ⟶ D) (j : D ⟶ P)
    (CK DK FK : Over BK) (eK : CK ⟶ DK) (jK : DK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left)
    (F : Over T) (π : F.left ⟶ P.left) (hπ : IsPullback π F.hom P.hom κ)
    (qF : FK.left ⟶ F.left)
    (qCT : CK.left ⟶ pullback κ C.hom) (qDT : DK.left ⟶ pullback κ D.hom) : Prop :=
  qCT ≫ pullback.fst κ C.hom = CK.hom ≫ ρ ∧
  qCT ≫ pullback.snd κ C.hom = qC ∧
  IsPullback qCT CK.hom (pullback.fst κ C.hom) ρ ∧
  qDT ≫ pullback.fst κ D.hom = DK.hom ≫ ρ ∧
  qDT ≫ pullback.snd κ D.hom = qD ∧
  IsPullback qDT DK.hom (pullback.fst κ D.hom) ρ ∧
  qCT ≫ (chosenScalarArrow κ e).left = eK.left ≫ qDT ∧
  qDT ≫ (scalarFlagInclusion κ D P j F π hπ).left = jK.left ≫ qF ∧
  IsProper (chosenScalarArrow κ e).left ∧
  IsClosedImmersion (scalarFlagInclusion κ D P j F π hπ).left

private theorem final_scalar_extension {B BK T : Scheme.{u}}
    (κ : T ⟶ B) (ρ : BK ⟶ T) (σ : BK ⟶ B) (hρ : ρ ≫ κ = σ)
    (C D P : Over B) (e : C ⟶ D) (j : D ⟶ P)
    [IsProper e.left] [IsClosedImmersion j.left]
    (CK DK FK : Over BK) (eK : CK ⟶ DK) (jK : DK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left)
    (qP : FK.left ⟶ P.left)
    (hC : IsPullback qC CK.hom C.hom σ) (hD : IsPullback qD DK.hom D.hom σ)
    (he : qC ≫ e.left = eK.left ≫ qD) (hj : qD ≫ j.left = jK.left ≫ qP)
    (F : Over T) (π : F.left ⟶ P.left) (hπ : IsPullback π F.hom P.hom κ)
    (qF : FK.left ⟶ F.left) (hFf : qF ≫ F.hom = FK.hom ≫ ρ)
    (hFs : qF ≫ π = qP) :
    ∃ (qCT : CK.left ⟶ pullback κ C.hom) (qDT : DK.left ⟶ pullback κ D.hom),
      FinalScalarFacts κ ρ C D P e j CK DK FK eK jK qC qD F π hπ qF qCT qDT := by
  let E : F ≅ Over.mk (pullback.fst κ P.hom) := hπ.flip.isoOverPullback
  let qCanon : FK.left ⟶ pullback κ P.hom := qF ≫ E.hom.left
  have hf : qCanon ≫ pullback.fst κ P.hom = FK.hom ≫ ρ := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => qF ≫ z) E.hom.w).trans hFf)
  have hs : qCanon ≫ pullback.snd κ P.hom = qP := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => qF ≫ z)
        hπ.flip.isoOverPullback_hom_left_comp_snd).trans hFs)
  obtain ⟨qCT, hCf, hCs, hCc⟩ := source_scalar_square κ ρ σ CK.hom C.hom qC hρ hC
  obtain ⟨qDT, hDf, hDs, hDc⟩ := source_scalar_square κ ρ σ DK.hom D.hom qD hρ hD
  have heT := scalar_triangle κ ρ e eK qC qD he qCT qDT hCf hCs hDf hDs
  have hjT := scalar_triangle κ ρ j jK qD qP hj qDT qCanon hDf hDs hf hs
  have hE : E.hom.left ≫ E.inv.left = 𝟙 F.left :=
    congrArg Over.Hom.left E.hom_inv_id
  have hjF : qDT ≫ (scalarFlagInclusion κ D P j F π hπ).left = jK.left ≫ qF :=
    triangle_cancel qDT (chosenScalarArrow κ j).left jK.left qF
      E.hom.left E.inv.left hE hjT
  let : IsProper (chosenScalarArrow κ e).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (scalarArrow_isPullback κ e).flip
      inferInstance
  let : IsClosedImmersion (chosenScalarArrow κ j).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (scalarArrow_isPullback κ j).flip
      inferInstance
  have hjFT : IsClosedImmersion (scalarFlagInclusion κ D P j F π hπ).left := by
    change IsClosedImmersion ((chosenScalarArrow κ j).left ≫ E.inv.left)
    infer_instance
  exact ⟨qCT, qDT, hCf, hCs, hCc, hDf, hDs, hDc, heT, hjF, inferInstance, hjFT⟩

private def PartialFamilyModels {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {I : Type v} {J : Type u} (G : ReductiveGroupData K) (s : J → G.rootBase.support)
    (S : Subalgebra ℤ K) (start : CoefficientStage S)
    (A D : I → Over (Spec (.of S))) (F : Over (Spec (.of S)))
    (AK DK : I → Over (Spec (.of K)))
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ (flagVariety G).toOver)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left)
    (qF : (flagVariety G).scheme ⟶ F.left) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k) (l : CoefficientStage k.val)
    (Q : J → Over (Spec (.of l.val)))
    (π : ∀ r, stageScalarModel k.val (stageScalarModel S F.hom k).hom l ⟶ Q r)
    (mF : (flagVariety G).scheme ⟶
      (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).left)
    (mQ : ∀ r, (partialFlagVariety G {s r}).scheme ⟶ (Q r).left),
    mF ≫ pullback.snd _ (stageScalarModel S F.hom k).hom ≫
      pullback.snd _ F.hom = qF ∧
    IsPullback mF (flagVariety G).toSpec
      (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).hom
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
    (∀ r, LocallyOfFinitePresentation (Q r).hom ∧
      LocallyOfFinitePresentation (π r).left ∧ QuasiCompact (π r).left ∧
      IsSeparated (π r).left ∧
      IsPullback (mQ r) (partialFlagVariety G {s r}).toSpec (Q r).hom
        (Spec.map (CommRingCat.ofHom (algebraMap l.val K))) ∧
      IsPullback (partialFlagMorphism G {s r}).left mF (mQ r) (π r).left) ∧
    DoubleFamilyFacts
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K)))
      A D F AK DK (flagVariety G).toOver e j eK jK qA qD mF

private theorem partial_family_models {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] {I : Type v} {J : Type u} [Finite J]
    (G : ReductiveGroupData K) (s : J → G.rootBase.support)
    (S : Subalgebra ℤ K) (start : CoefficientStage S)
    (A D : I → Over (Spec (.of S))) (F : Over (Spec (.of S)))
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (AK DK : I → Over (Spec (.of K)))
    (e : ∀ i, A i ⟶ D i) (j : ∀ i, D i ⟶ F)
    [∀ i, IsProper (e i).left] [∀ i, IsClosedImmersion (j i).left]
    (eK : ∀ i, AK i ⟶ DK i) (jK : ∀ i, DK i ⟶ (flagVariety G).toOver)
    (qA : ∀ i, (AK i).left ⟶ (A i).left)
    (qD : ∀ i, (DK i).left ⟶ (D i).left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hA : ∀ i, IsPullback (qA i) (AK i).hom (A i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : ∀ i, IsPullback (qD i) (DK i).hom (D i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : ∀ i, qA i ≫ (e i).left = (eK i).left ≫ qD i)
    (hj : ∀ i, qD i ≫ (j i).left = (jK i).left ≫ qF) :
    PartialFamilyModels G s S start A D F AK DK e j eK jK qA qD qF := by
  obtain ⟨k, hk, l, Q, π, mF, mQ, hOld, hFcart, hQ⟩ :=
    exists_word_partial_flags G s S start F qF hF
  have hFf : mF ≫ (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).hom =
      (flagVariety G).toSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap l.val K)) :=
    hFcart.w
  have hFamily := double_endpoint_family
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap l.val K)))
    (Spec.map (CommRingCat.ofHom (algebraMap k.val K)))
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (coefficient_triangle k.val l.val l.property.2)
    (coefficient_triangle S k.val k.property.2)
    A D F AK DK (flagVariety G).toOver e j eK jK qA qD qF hA hD hF he hj mF hFf hOld
  exact ⟨k, hk, l, Q, π, mF, mQ, hOld, hFcart, hQ, hFamily⟩

private def familyWord {T : Type u} (word : List T) : Option (Fin word.length) → List T
  | none => word
  | some p => word.take p.val

private theorem family_reduced {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    ∀ t, (weylCoxeterSystem G.rootBase).IsReduced (familyWord word t)
  | none => hred
  | some p => hred.take p.val

private def WordPartialData {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S))) (start : CoefficientStage S)
    (qP : (flagVariety G).scheme ⟶ P.left)
    (C D : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    (qC : bsdhScheme G word ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase word)).scheme ⟶ D.left) : Prop :=
  ∃ d : PrefixEndpointData G (fun p : Fin word.length => word.take p.val)
      (fun p => hred.take p.val) S P start qP,
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (PrefixEndpointData.original_le
    d)).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap (PrefixEndpointData.coefficient d) K))
  let CT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ C.hom)
  let DT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ D.hom)
  let eT := chosenScalarArrow κ e
  let jT := scalarFlagInclusion κ D P j (PrefixEndpointData.flag d) (PrefixEndpointData.projection
    d) (PrefixEndpointData.projection_square d)
  ∃ (qCT : bsdhScheme G word ⟶ CT.left)
    (qDT : (schubertVariety G (simpleWeylWord G.rootBase word)).scheme ⟶ DT.left),
  FinalScalarFacts κ ρ C D P e j (bsdhVariety G word).toOver
    (schubertVariety G (simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
    (bsdhSchubertMap G word hred) (schubertInclusion G (simpleWeylWord G.rootBase word))
    qC qD (PrefixEndpointData.flag d) (PrefixEndpointData.projection d)
      (PrefixEndpointData.projection_square d) (PrefixEndpointData.flagComparison d) qCT qDT ∧
  let A : Option (Fin word.length) → Over (Spec (.of (PrefixEndpointData.coefficient d))) :=
    fun t => t.elim CT (PrefixEndpointData.source d)
  let B : Option (Fin word.length) → Over (Spec (.of (PrefixEndpointData.coefficient d))) :=
    fun t => t.elim DT (PrefixEndpointData.target d)
  let a : ∀ t, A t ⟶ B t := fun t => match t with
    | none => eT
    | some p => (PrefixEndpointData.endpoint d) p
  let b : ∀ t, B t ⟶ (PrefixEndpointData.flag d) := fun t => match t with
    | none => jT
    | some p => (PrefixEndpointData.inclusion d) p
  let AK := fun t => (bsdhVariety G (familyWord word t)).toOver
  let BK := fun t => (schubertVariety G (simpleWeylWord G.rootBase (familyWord word t))).toOver
  let aK := fun t => bsdhSchubertMap G (familyWord word t) (family_reduced G word hred t)
  let bK := fun t => schubertInclusion G (simpleWeylWord G.rootBase (familyWord word t))
  let qA : ∀ t, (AK t).left ⟶ (A t).left := fun t => match t with
    | none => qCT
    | some p => (PrefixEndpointData.sourceComparison d) p
  let qB : ∀ t, (BK t).left ⟶ (B t).left := fun t => match t with
    | none => qDT
    | some p => (PrefixEndpointData.targetComparison d) p
  PartialFamilyModels G (fun p : ULift.{u} (Fin word.length) => word.get p.down)
    (PrefixEndpointData.coefficient d) ⟨(PrefixEndpointData.coefficient d),
      (PrefixEndpointData.finiteGeneration d), le_rfl⟩ A B (PrefixEndpointData.flag d) AK BK a b aK
      bK
    qA qB (PrefixEndpointData.flagComparison d)

/-- The strict prefixes and a given final endpoint have a shared arithmetic
diagram with all simple partial-flag projections. The given endpoint and its
target are only extended by the displayed coefficient maps, and every
comparison with the original model is retained. -/
theorem exists_word_partial_diagram {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (qP : (flagVariety G).scheme ⟶ P.left)
    (hP : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (C D : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    [IsProper e.left] [IsClosedImmersion j.left]
    (qC : bsdhScheme G word ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase word)).scheme ⟶ D.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (schubertVariety G (simpleWeylWord G.rootBase word)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = (bsdhSchubertMap G word hred).left ≫ qD)
    (hj : qD ≫ j.left = (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qP)
    (start : CoefficientStage S) :
    WordPartialData G word hred S P start qP C D e j qC qD := by
  classical
  obtain ⟨d⟩ := exists_word_prefix_diagram G word hred S hS P qP hP start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (PrefixEndpointData.original_le
    d)).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap (PrefixEndpointData.coefficient d) K))
  let CT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ C.hom)
  let DT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ D.hom)
  let eT := chosenScalarArrow κ e
  let jT := scalarFlagInclusion κ D P j (PrefixEndpointData.flag d) (PrefixEndpointData.projection
    d) (PrefixEndpointData.projection_square d)
  obtain ⟨qCT, qDT, hf⟩ := final_scalar_extension κ ρ
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (coefficient_triangle S (PrefixEndpointData.coefficient d) (PrefixEndpointData.original_le d)) C
      D P e j
    (bsdhVariety G word).toOver
    (schubertVariety G (simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
    (bsdhSchubertMap G word hred) (schubertInclusion G (simpleWeylWord G.rootBase word))
    qC qD qP hC hD he hj (PrefixEndpointData.flag d) (PrefixEndpointData.projection d)
      (PrefixEndpointData.projection_square d) (PrefixEndpointData.flagComparison d)
    (PrefixEndpointData.flag_square d).w (PrefixEndpointData.flag_original d)
  let A : Option (Fin word.length) → Over (Spec (.of (PrefixEndpointData.coefficient d))) :=
    fun t => t.elim CT (PrefixEndpointData.source d)
  let B : Option (Fin word.length) → Over (Spec (.of (PrefixEndpointData.coefficient d))) :=
    fun t => t.elim DT (PrefixEndpointData.target d)
  let a : ∀ t, A t ⟶ B t := fun t => match t with
    | none => eT
    | some p => (PrefixEndpointData.endpoint d) p
  let b : ∀ t, B t ⟶ (PrefixEndpointData.flag d) := fun t => match t with
    | none => jT
    | some p => (PrefixEndpointData.inclusion d) p
  let AK := fun t => (bsdhVariety G (familyWord word t)).toOver
  let BK := fun t => (schubertVariety G (simpleWeylWord G.rootBase (familyWord word t))).toOver
  let aK := fun t => bsdhSchubertMap G (familyWord word t) (family_reduced G word hred t)
  let bK := fun t => schubertInclusion G (simpleWeylWord G.rootBase (familyWord word t))
  let qA : ∀ t, (AK t).left ⟶ (A t).left := fun t => match t with
    | none => qCT
    | some p => (PrefixEndpointData.sourceComparison d) p
  let qB : ∀ t, (BK t).left ⟶ (B t).left := fun t => match t with
    | none => qDT
    | some p => (PrefixEndpointData.targetComparison d) p
  let : LocallyOfFinitePresentation (PrefixEndpointData.flag d).hom :=
    (PrefixEndpointData.flag_presentation d)
  let : QuasiCompact (PrefixEndpointData.flag d).hom := (PrefixEndpointData.flag_compact d)
  let : IsSeparated (PrefixEndpointData.flag d).hom := (PrefixEndpointData.flag_separated d)
  let : ∀ t, IsProper (a t).left := fun t => by
    cases t with
    | none => exact hf.2.2.2.2.2.2.2.2.1
    | some p => exact (PrefixEndpointData.endpoint_proper d) p
  let : ∀ t, IsClosedImmersion (b t).left := fun t => by
    cases t with
    | none => exact hf.2.2.2.2.2.2.2.2.2
    | some p => exact (PrefixEndpointData.inclusion_closed d) p
  have hA : ∀ t, IsPullback (qA t) (AK t).hom (A t).hom ρ := by
    intro t
    cases t with
    | none => exact hf.2.2.1
    | some p => exact (PrefixEndpointData.source_square d) p
  have hB : ∀ t, IsPullback (qB t) (BK t).hom (B t).hom ρ := by
    intro t
    cases t with
    | none => exact hf.2.2.2.2.2.1
    | some p => exact (PrefixEndpointData.target_square d) p
  have ha : ∀ t, qA t ≫ (a t).left = (aK t).left ≫ qB t := by
    intro t
    cases t with
    | none => exact hf.2.2.2.2.2.2.1
    | some p => exact (PrefixEndpointData.endpoint_comparison d) p
  have hb : ∀ t, qB t ≫ (b t).left = (bK t).left ≫ (PrefixEndpointData.flagComparison d) := by
    intro t
    cases t with
    | none => exact hf.2.2.2.2.2.2.2.1
    | some p => exact (PrefixEndpointData.inclusion_comparison d) p
  have hModels := partial_family_models G (fun p : ULift.{u} (Fin word.length) => word.get p.down)
    (PrefixEndpointData.coefficient d) ⟨(PrefixEndpointData.coefficient d),
      (PrefixEndpointData.finiteGeneration d), le_rfl⟩ A B (PrefixEndpointData.flag d) AK BK a b aK
      bK
    qA qB (PrefixEndpointData.flagComparison d) hA hB (PrefixEndpointData.flag_square d) ha hb
  exact ⟨d, qCT, qDT, hf, hModels⟩

end SchubertGeometry
