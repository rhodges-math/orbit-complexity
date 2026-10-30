import OrbitComplexity.SchubertGeometry.Connectedness.WordPartialDiagram
import OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
import OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
import Mathlib.Data.List.Induction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficient-retaining induction for word endpoints

An appended endpoint is compared with the scalar extension of its
predecessor. Connectedness enters the successor construction only through
that predecessor, and scalar towers preserve the original endpoint.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private scalar_model scalar_property scalar_fp scalar_qc
  stage_map stage_map_cartesian stage_map_original scalar_comparison
  scalar_composite_comparison scalar_square scalar_tower_gc change_scalar_gc
  spec_triangle field_connected
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private WordPartialData scalarFlagInclusion
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPartialDiagram
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

private theorem endpoint_factor {C : Type v} [Category C]
    {A B D X Y Z : C} (qX : A ⟶ X) (qY : B ⟶ Y) (qF : D ⟶ Z)
    (e : X ⟶ Y) (j : Y ⟶ Z) (f : A ⟶ B) (g : B ⟶ D)
    (he : qX ≫ e = f ≫ qY) (hj : qY ≫ j = g ≫ qF) :
    qX ≫ (e ≫ j) = (f ≫ g) ≫ qF := by
  rw [← Category.assoc, he, Category.assoc, hj, ← Category.assoc]

private theorem coefficient_comp {K : Type u} [CommRing K]
    {S T R : Subalgebra ℤ K} (hST : S ≤ T) (hTR : T ≤ R) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTR).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hST.trans hTR)).toRingHom) :=
  spec_triangle (Subalgebra.inclusion hST).toRingHom
    (Subalgebra.inclusion hTR).toRingHom
    (Subalgebra.inclusion (hST.trans hTR)).toRingHom (by ext x; rfl)

private theorem scalar_endpoint_gc {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Over (Spec (.of S))} (e : X ⟶ Y)
    (k : CoefficientStage S) (l : CoefficientStage k.val)
    (h : GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          e)).left) :
    GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (k.property.2.trans l.property.2)).toRingHom)) e).left :=
  change_scalar_gc (coefficient_comp k.property.2 l.property.2) e
    (scalar_tower_gc _ _ e h)

/-- A connected scalar extension of the predecessor endpoint yields a later
connected scalar extension of the given appended endpoint. The coefficient
extension is taken above the predecessor's stage. -/
theorem exists_scalar_endpoint_step
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    {N A Y Z F Q : Over (Spec (.of S))}
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [LocallyOfFinitePresentation Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom]
    [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left]
    (m : N ⟶ Z) (z : Z ⟶ F) [IsClosedImmersion z.left] (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qZ : (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶ Z.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hZ : IsPullback qZ
      (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec Z.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ (m ≫ z).left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hz : qZ ≫ z.left =
      (schubertInclusion G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫ qF)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (k : CoefficientStage S)
    (hprev : GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) f).left) :
    ∃ (l : CoefficientStage S) (_ : k ≤ l),
      GeometricallyConnected
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)) m).left := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let NK := (bsdhVariety G (word ++ [i])).toOver
  let AK := (bsdhVariety G word).toOver
  let YK := (schubertVariety G v).toOver
  let ZK := (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let FK := (flagVariety G).toOver
  let QK := (partialFlagVariety G {i}).toOver
  let nK : NK ⟶ FK := Over.homMk (bsdhMap G (word ++ [i])) rfl
  let aK : AK ⟶ FK := Over.homMk (bsdhMap G word) rfl
  let qNk := stage_map S N NK qN hN k
  let qAk := stage_map S A AK qA hA k
  let qYk := stage_map S Y YK qY hY k
  let qZk := stage_map S Z ZK qZ hZ k
  let qFk := stage_map S F FK qF hF k
  let qQk := stage_map S Q QK qQ hQ k
  have hNk := stage_map_cartesian S N NK qN hN k
  have hAk := stage_map_cartesian S A AK qA hA k
  have hYk := stage_map_cartesian S Y YK qY hY k
  have hZk := stage_map_cartesian S Z ZK qZ hZ k
  have hFk := stage_map_cartesian S F FK qF hF k
  have hQk := stage_map_cartesian S Q QK qQ hQ k
  have hNo := stage_map_original S N NK qN hN k
  have hAo := stage_map_original S A AK qA hA k
  have hYo := stage_map_original S Y YK qY hY k
  have hZo := stage_map_original S Z ZK qZ hZ k
  have hFo := stage_map_original S F FK qF hF k
  have hQo := stage_map_original S Q QK qQ hQ k
  have hnk₀ := scalar_comparison κ ρ (m ≫ z) nK qN qF
    qNk qFk hNk hFk hNo hFo hn
  have hnk := scalar_composite_comparison κ m z nK.left qNk qFk hnk₀
  have hak₀ := scalar_comparison κ ρ (f ≫ j) aK qA qF
    qAk qFk hAk hFk hAo hFo ha.symm
  have hak := scalar_composite_comparison κ f j aK.left qAk qFk hak₀
  have hjk := scalar_comparison κ ρ j (schubertInclusion G v) qY qF
    qYk qFk hYk hFk hYo hFo hj.symm
  have hzk := scalar_comparison κ ρ z
    (schubertInclusion G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) qZ qF
    qZk qFk hZk hFk hZo hFo hz
  have hπcomm := scalar_comparison κ ρ π (partialFlagMorphism G {i}) qF qQ
    qFk qQk hFk hQk hFo hQo hπ.w.symm
  have hπk := scalar_square κ π (partialFlagMorphism G {i}) qF qQ hπ
    qFk qQk hFo hQo hπcomm
  let fk : scalar_model κ A ⟶ scalar_model κ Y := chosenScalarArrow κ f
  let jk : scalar_model κ Y ⟶ scalar_model κ F := chosenScalarArrow κ j
  let mk : scalar_model κ N ⟶ scalar_model κ Z := chosenScalarArrow κ m
  let zk : scalar_model κ Z ⟶ scalar_model κ F := chosenScalarArrow κ z
  let πk : scalar_model κ F ⟶ scalar_model κ Q := chosenScalarArrow κ π
  let : LocallyOfFinitePresentation (scalar_model κ N).hom := scalar_fp κ N
  let : QuasiCompact (scalar_model κ N).hom := scalar_qc κ N
  let : LocallyOfFinitePresentation (scalar_model κ A).hom := scalar_fp κ A
  let : QuasiCompact (scalar_model κ A).hom := scalar_qc κ A
  let : LocallyOfFinitePresentation (scalar_model κ Z).hom := scalar_fp κ Z
  let : QuasiCompact (scalar_model κ Z).hom := scalar_qc κ Z
  let : IsSeparated (scalar_model κ Z).hom := by
    change IsSeparated (pullback.fst κ Z.hom)
    infer_instance
  let : LocallyOfFinitePresentation (scalar_model κ F).hom := scalar_fp κ F
  let : QuasiCompact (scalar_model κ F).hom := scalar_qc κ F
  let : LocallyOfFinitePresentation (scalar_model κ Q).hom := scalar_fp κ Q
  let : IsProper fk.left :=
    scalar_property (@IsProper) κ f inferInstance
  let : GeometricallyConnected fk.left := hprev
  let : IsClosedImmersion jk.left :=
    scalar_property (@IsClosedImmersion) κ j inferInstance
  let : IsClosedImmersion zk.left :=
    scalar_property (@IsClosedImmersion) κ z inferInstance
  let : LocallyOfFinitePresentation πk.left :=
    scalar_property (@LocallyOfFinitePresentation) κ π inferInstance
  let : QuasiCompact πk.left :=
    scalar_property (@QuasiCompact) κ π inferInstance
  let : IsSeparated πk.left :=
    scalar_property (@IsSeparated) κ π inferInstance
  obtain ⟨l, _hl, _hbase, _hold, hgc, _hfields⟩ := exists_append_schubert_connected
    k.val k.property.1 G word v i hv
    (N := scalar_model κ N) (A := scalar_model κ A)
    (Y := scalar_model κ Y) (Z := scalar_model κ Z)
    (F := scalar_model κ F) (Q := scalar_model κ Q)
    fk jk mk zk πk
    qNk qAk qYk qZk qFk qQk hNk hAk hYk hZk hFk hQk
    hnk hak.symm hjk.symm hzk hπk ⟨k.val, k.property.1, le_rfl⟩
  exact ⟨⟨l.val, l.property.1, k.property.2.trans l.property.2⟩,
    l.property.2, scalar_endpoint_gc S m k l hgc⟩

private theorem over_property {B : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : Over B} (f : X ⟶ Y) (h : P (f.left ≫ Y.hom)) : P X.hom :=
  f.w ▸ h

private theorem endpoint_properties (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C D F : Over (Spec (.of R))) (e : C ⟶ D) (j : D ⟶ F)
    [IsProper e.left] [IsClosedImmersion j.left]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom] :
    LocallyOfFinitePresentation C.hom ∧ QuasiCompact C.hom ∧
      LocallyOfFinitePresentation D.hom ∧ QuasiCompact D.hom ∧ IsSeparated D.hom := by
  let : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  let : IsLocallyNoetherian D.left := LocallyOfFiniteType.isLocallyNoetherian j.left
  let : LocallyOfFinitePresentation j.left := inferInstance
  let : LocallyOfFinitePresentation e.left := inferInstance
  have hDfp : LocallyOfFinitePresentation D.hom := by
    exact over_property (@LocallyOfFinitePresentation) j inferInstance
  have hDqc : QuasiCompact D.hom := by
    exact over_property (@QuasiCompact) j inferInstance
  have hDsep : IsSeparated D.hom := by
    exact over_property (@IsSeparated) j inferInstance
  let : LocallyOfFinitePresentation D.hom := hDfp
  let : QuasiCompact D.hom := hDqc
  refine ⟨?_, ?_, hDfp, hDqc, hDsep⟩
  · exact over_property (@LocallyOfFinitePresentation) e inferInstance
  · exact over_property (@QuasiCompact) e inferInstance

open private double_endpoint_family
  from OrbitComplexity.SchubertGeometry.Connectedness.WordPartialDiagram
open private coefficient_triangle
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointModels

private theorem stage_endpoint_data {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (k : CoefficientStage S) (l : CoefficientStage k.val)
    (A D F : Over (Spec (.of S))) (e : A ⟶ D) (j : D ⟶ F)
    [IsProper e.left] [IsClosedImmersion j.left]
    (X Y FK : Over (Spec (.of K))) (eK : X ⟶ Y) (jK : Y ⟶ FK)
    (qX : X.left ⟶ A.left) (qY : Y.left ⟶ D.left) (qF : FK.left ⟶ F.left)
    (hX : IsPullback qX X.hom A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY Y.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF FK.hom F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qX ≫ e.left = eK.left ≫ qY)
    (hj : qY ≫ j.left = jK.left ≫ qF)
    (mF : FK.left ⟶ (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).left)
    (hFl : IsPullback mF FK.hom
      (stageScalarModel k.val (stageScalarModel S F.hom k).hom l).hom
      (Spec.map (CommRingCat.ofHom (algebraMap l.val K))))
    (hold : mF ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
        (stageScalarModel S F.hom k).hom ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) F.hom = qF) :
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
    let ρ := Spec.map (CommRingCat.ofHom (algebraMap l.val K))
    let A₁ := stageScalarModel S A.hom k
    let D₁ := stageScalarModel S D.hom k
    let A₂ := stageScalarModel k.val A₁.hom l
    let D₂ := stageScalarModel k.val D₁.hom l
    ∃ (qX₂ : X.left ⟶ A₂.left) (qY₂ : Y.left ⟶ D₂.left),
      IsPullback qX₂ X.hom A₂.hom ρ ∧
      IsPullback qY₂ Y.hom D₂.hom ρ ∧
      qX₂ ≫ (chosenScalarArrow τ (chosenScalarArrow κ e)).left = eK.left ≫ qY₂ ∧
      qY₂ ≫ (chosenScalarArrow τ (chosenScalarArrow κ j)).left = jK.left ≫ mF ∧
      IsProper (chosenScalarArrow τ (chosenScalarArrow κ e)).left ∧
      IsClosedImmersion (chosenScalarArrow τ (chosenScalarArrow κ j)).left ∧
      qX₂ ≫ pullback.snd τ A₁.hom ≫ pullback.snd κ A.hom = qX ∧
      qY₂ ≫ pullback.snd τ D₁.hom ≫ pullback.snd κ D.hom = qY := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap l.val K))
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let η := Spec.map (CommRingCat.ofHom (algebraMap S K))
  have hρ : ρ ≫ τ = σ := coefficient_triangle k.val l.val l.property.2
  have hσ : σ ≫ κ = η := coefficient_triangle S k.val k.property.2
  obtain ⟨qX₁, qY₁, qX₂, qY₂, h₁, h₂⟩ :=
    double_endpoint_family κ τ ρ σ η hρ hσ
      (fun _ : Unit => A) (fun _ : Unit => D) F
      (fun _ : Unit => X) (fun _ : Unit => Y) FK
      (fun _ => e) (fun _ => j) (fun _ => eK) (fun _ => jK)
      (fun _ => qX) (fun _ => qY) qF
      (fun _ => hX) (fun _ => hY) hF (fun _ => he) (fun _ => hj)
      mF hFl.w hold
  rcases h₁.2 () with ⟨_, hX₁old, _, _, hY₁old, _, _, _, _, _⟩
  rcases h₂.2 () with ⟨_, hX₂old, hX₂, _, hY₂old, hY₂, he₂, hj₂, hp₂, hc₂⟩
  refine ⟨qX₂ (), qY₂ (), hX₂, hY₂, he₂, hj₂, hp₂, hc₂, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ pullback.snd κ A.hom) hX₂old)).trans hX₁old
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ pullback.snd κ D.hom) hY₂old)).trans hY₁old


private theorem stage_properties {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (X : Over (Spec (.of S))) (k : CoefficientStage S)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    LocallyOfFinitePresentation (stageScalarModel S X.hom k).hom ∧
      QuasiCompact (stageScalarModel S X.hom k).hom ∧
      IsSeparated (stageScalarModel S X.hom k).hom := by
  change LocallyOfFinitePresentation (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom) ∧
    QuasiCompact (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom) ∧
    IsSeparated (pullback.fst
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem word_endpoint_reindex {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {word word' : List G.rootBase.support}
    (hword : word = word')
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hred' : (weylCoxeterSystem G.rootBase).IsReduced word')
    {B : Scheme.{u}} (A D F : Over B) (e : A ⟶ D) (j : D ⟶ F)
    (qF : (flagVariety G).toOver.left ⟶ F.left) (ρ : Spec (.of K) ⟶ B)
    (qA : (bsdhVariety G word).toOver.left ⟶ A.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase word)).toOver.left ⟶ D.left)
    (hA : IsPullback qA (bsdhVariety G word).toOver.hom A.hom ρ)
    (hD : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase word)).toOver.hom D.hom ρ)
    (he : qA ≫ e.left = (bsdhSchubertMap G word hred).left ≫ qD)
    (hj : qD ≫ j.left =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qF) :
    ∃ (qA' : bsdhScheme G word' ⟶ A.left)
      (qD' : (schubertVariety G (simpleWeylWord G.rootBase word')).scheme ⟶ D.left),
      IsPullback qA' (bsdhToSpec G word') A.hom ρ ∧
      IsPullback qD'
        (schubertVariety G (simpleWeylWord G.rootBase word')).toSpec D.hom ρ ∧
      qA' ≫ e.left = (bsdhSchubertMap G word' hred').left ≫ qD' ∧
      qD' ≫ j.left =
        (schubertInclusion G (simpleWeylWord G.rootBase word')).left ≫ qF := by
  cases hword
  exact ⟨qA, qD, hA, hD, he, hj⟩


private theorem target_reindex {B BK : Scheme.{u}} {T : Type v}
    (Y : T → Over BK) (FK : Over BK) (jK : ∀ t, Y t ⟶ FK)
    {a b : T} (h : a = b) (D F : Over B) (j : D ⟶ F)
    (qF : FK.left ⟶ F.left) (ρ : BK ⟶ B)
    (qD : (Y a).left ⟶ D.left) (hD : IsPullback qD (Y a).hom D.hom ρ)
    (hj : qD ≫ j.left = (jK a).left ≫ qF) :
    ∃ qD' : (Y b).left ⟶ D.left, IsPullback qD' (Y b).hom D.hom ρ ∧
      qD' ≫ j.left = (jK b).left ≫ qF := by
  cases h
  exact ⟨qD, hD, hj⟩

private theorem projection_reindex {B BK : Scheme.{u}} {T : Type v}
    (FK : Over BK) (QK : T → Over BK) (πK : ∀ t, FK ⟶ QK t)
    {a b : T} (h : a = b) (F Q : Over B) (π : F ⟶ Q)
    (qF : FK.left ⟶ F.left) (ρ : BK ⟶ B)
    (qQ : (QK a).left ⟶ Q.left) (hQ : IsPullback qQ (QK a).hom Q.hom ρ)
    (hπ : IsPullback (πK a).left qF qQ π.left) :
    ∃ qQ' : (QK b).left ⟶ Q.left, IsPullback qQ' (QK b).hom Q.hom ρ ∧
      IsPullback (πK b).left qF qQ' π.left := by
  cases h
  exact ⟨qQ, hQ, hπ⟩

private theorem reduced_append_left {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced (word ++ [i])) :
    (weylCoxeterSystem G.rootBase).IsReduced word := by
  simpa only [List.take_append_length] using hred.take word.length

private theorem append_get_last {T : Type v} (word : List T) (i : T) :
    (word ++ [i]).get ⟨word.length, by simp⟩ = i := by
  simp [List.get_eq_getElem]

private theorem append_ascent {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced (word ++ [i])) :
    (weylCoxeterSystem G.rootBase).length (simpleWeylWord G.rootBase word) <
      (weylCoxeterSystem G.rootBase).length
        (simpleWeylWord G.rootBase word * RootPairing.weylGroup.ofIdx G.rootSystem i.val) := by
  have hprev : (weylCoxeterSystem G.rootBase).IsReduced word := by
    simpa only [List.take_append_length] using hred.take word.length
  have hp := (weylCoxeterSystem_isReduced_iff G.rootBase word).mp hprev
  have ht := (weylCoxeterSystem_isReduced_iff G.rootBase (word ++ [i])).mp hred
  rw [simpleWeylWord_append_singleton, List.length_append, List.length_singleton] at ht
  simp only [weylCoxeterSystem_length]
  omega

private def ConnectedEndpoint {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {C D : Over (Spec (.of S))} (e : C ⟶ D)
    (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k),
    GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) e).left

private def wordEndpointConnected {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) : Prop :=
  ∀ (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (_ : S.FG) (P : Over (Spec (.of S)))
    (_ : LocallyOfFinitePresentation P.hom) (_ : QuasiCompact P.hom) (_ : IsSeparated P.hom)
    (qP : (flagVariety G).scheme ⟶ P.left)
    (_ : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (C D : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    (_ : IsProper e.left) (_ : IsClosedImmersion j.left)
    (qC : bsdhScheme G word ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase word)).scheme ⟶ D.left)
    (_ : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (_ : IsPullback qD (schubertVariety G (simpleWeylWord G.rootBase word)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (_ : qC ≫ e.left = (bsdhSchubertMap G word hred).left ≫ qD)
    (_ : qD ≫ j.left =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qP)
    (start : CoefficientStage S), ConnectedEndpoint S e start


private theorem successor_from_partial {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (ih : wordEndpointConnected G word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced (word ++ [i]))
    (S : Subalgebra ℤ K) (P : Over (Spec (.of S)))
    (qP : (flagVariety G).scheme ⟶ P.left)
    (C D : Over (Spec (.of S))) (e : C ⟶ D) (j₀ : D ⟶ P)
    (qC : bsdhScheme G (word ++ [i]) ⟶ C.left)
    (qD : (schubertVariety G (simpleWeylWord G.rootBase (word ++ [i]))).scheme ⟶ D.left)
    (start : CoefficientStage S)
    (hp : WordPartialData G (word ++ [i]) hred S P start qP C D e j₀ qC qD) :
    ConnectedEndpoint S e start := by
  classical
  rcases hp with ⟨d, qCT, qDT, hfinal, k, _hk, l, Q, π, mF, mQ,
    hOld, hFcart, hQ, _hDouble⟩
  let κ₀ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (PrefixEndpointData.original_le
    d)).toRingHom)
  let κ₁ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let κ₂ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap l.val K))
  let p : Fin (word ++ [i]).length := ⟨word.length, by simp⟩
  let CT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ₀ C.hom)
  let DT : Over (Spec (.of (PrefixEndpointData.coefficient d))) := Over.mk (pullback.fst κ₀ D.hom)
  let eT := chosenScalarArrow κ₀ e
  let jT := scalarFlagInclusion κ₀ D P j₀ (PrefixEndpointData.flag d) (PrefixEndpointData.projection
    d) (PrefixEndpointData.projection_square d)
  let N := stageScalarModel k.val (stageScalarModel (PrefixEndpointData.coefficient d) CT.hom k).hom
    l
  let Z := stageScalarModel k.val (stageScalarModel (PrefixEndpointData.coefficient d) DT.hom k).hom
    l
  let A := stageScalarModel k.val (stageScalarModel (PrefixEndpointData.coefficient d)
    ((PrefixEndpointData.source d) p).hom k).hom l
  let Y := stageScalarModel k.val (stageScalarModel (PrefixEndpointData.coefficient d)
    ((PrefixEndpointData.target d) p).hom k).hom l
  let F := stageScalarModel k.val (stageScalarModel (PrefixEndpointData.coefficient d)
    (PrefixEndpointData.flag d).hom k).hom l
  let m : N ⟶ Z := chosenScalarArrow κ₂ (chosenScalarArrow κ₁ eT)
  let z : Z ⟶ F := chosenScalarArrow κ₂ (chosenScalarArrow κ₁ jT)
  let f : A ⟶ Y := chosenScalarArrow κ₂ (chosenScalarArrow κ₁ ((PrefixEndpointData.endpoint d) p))
  let j : Y ⟶ F := chosenScalarArrow κ₂ (chosenScalarArrow κ₁ ((PrefixEndpointData.inclusion d) p))
  rcases hfinal with ⟨_, _, hCT, _, _, hDT, heT, hjT, heProper, hjClosed⟩
  let : IsProper eT.left := heProper
  let : IsClosedImmersion jT.left := hjClosed
  obtain ⟨qNl, qZl, hNc, hZc, heN, hjZ, hm, hz, _hNOld, _hZOld⟩ :=
    stage_endpoint_data (PrefixEndpointData.coefficient d) k l CT DT
      (PrefixEndpointData.flag d) eT jT
      (bsdhVariety G (word ++ [i])).toOver
      (schubertVariety G (simpleWeylWord G.rootBase (word ++ [i]))).toOver
      (flagVariety G).toOver
      (bsdhSchubertMap G (word ++ [i]) hred)
      (schubertInclusion G (simpleWeylWord G.rootBase (word ++ [i])))
      qCT qDT (PrefixEndpointData.flagComparison d) hCT hDT
      (PrefixEndpointData.flag_square d) heT hjT mF hFcart hOld
  let : IsProper ((PrefixEndpointData.endpoint d) p).left :=
    (PrefixEndpointData.endpoint_proper d) p
  let : IsClosedImmersion ((PrefixEndpointData.inclusion d) p).left :=
    (PrefixEndpointData.inclusion_closed d) p
  obtain ⟨qAp, qDp, hAc, hYc, heA, hjY, hf, hj, _hApOld, _hDpOld⟩ :=
    stage_endpoint_data (PrefixEndpointData.coefficient d) k l
      ((PrefixEndpointData.source d) p) ((PrefixEndpointData.target d) p)
      (PrefixEndpointData.flag d) ((PrefixEndpointData.endpoint d) p)
      ((PrefixEndpointData.inclusion d) p)
      (bsdhVariety G ((word ++ [i]).take p.val)).toOver
      (schubertVariety G (simpleWeylWord G.rootBase ((word ++ [i]).take p.val))).toOver
      (flagVariety G).toOver
      (bsdhSchubertMap G ((word ++ [i]).take p.val) (hred.take p.val))
      (schubertInclusion G (simpleWeylWord G.rootBase ((word ++ [i]).take p.val)))
      ((PrefixEndpointData.sourceComparison d) p) ((PrefixEndpointData.targetComparison d) p)
      (PrefixEndpointData.flagComparison d)
      ((PrefixEndpointData.source_square d) p) ((PrefixEndpointData.target_square d) p)
      (PrefixEndpointData.flag_square d)
      ((PrefixEndpointData.endpoint_comparison d) p) ((PrefixEndpointData.inclusion_comparison d) p)
      mF hFcart hOld
  let : IsProper m.left := hm
  let : IsClosedImmersion z.left := hz
  let : IsProper f.left := hf
  let : IsClosedImmersion j.left := hj
  let : LocallyOfFinitePresentation (PrefixEndpointData.flag d).hom :=
    (PrefixEndpointData.flag_presentation d)
  let : QuasiCompact (PrefixEndpointData.flag d).hom := (PrefixEndpointData.flag_compact d)
  let : IsSeparated (PrefixEndpointData.flag d).hom := (PrefixEndpointData.flag_separated d)
  have hF₁ := stage_properties (PrefixEndpointData.coefficient d) (PrefixEndpointData.flag d) k
  let : LocallyOfFinitePresentation
      (stageScalarModel (PrefixEndpointData.coefficient d) (PrefixEndpointData.flag d).hom k).hom :=
    hF₁.1
  let : QuasiCompact
      (stageScalarModel (PrefixEndpointData.coefficient d) (PrefixEndpointData.flag d).hom k).hom :=
    hF₁.2.1
  let : IsSeparated
      (stageScalarModel (PrefixEndpointData.coefficient d) (PrefixEndpointData.flag d).hom k).hom :=
    hF₁.2.2
  have hFprop := stage_properties k.val
    (stageScalarModel (PrefixEndpointData.coefficient d) (PrefixEndpointData.flag d).hom k) l
  let : LocallyOfFinitePresentation F.hom := hFprop.1
  let : QuasiCompact F.hom := hFprop.2.1
  let : IsSeparated F.hom := hFprop.2.2
  let : Algebra.FiniteType ℤ l.val :=
    (Subalgebra.fg_iff_finiteType l.val).mp l.property.1
  let : IsNoetherianRing l.val := Algebra.FiniteType.isNoetherianRing ℤ l.val
  have hNprop := endpoint_properties l.val N Z F m z
  have hAprop := endpoint_properties l.val A Y F f j
  let : LocallyOfFinitePresentation N.hom := hNprop.1
  let : QuasiCompact N.hom := hNprop.2.1
  let : LocallyOfFinitePresentation Z.hom := hNprop.2.2.1
  let : QuasiCompact Z.hom := hNprop.2.2.2.1
  let : IsSeparated Z.hom := hNprop.2.2.2.2
  let : LocallyOfFinitePresentation A.hom := hAprop.1
  let : QuasiCompact A.hom := hAprop.2.1
  have hred₀ := reduced_append_left G word i hred
  obtain ⟨qA, qY, hA, hY, heA', hjY'⟩ :=
    word_endpoint_reindex G (word := (word ++ [i]).take p.val) (word' := word)
      List.take_append_length (hred.take p.val) hred₀
      A Y F f j mF ρ qAp qDp hAc hYc heA hjY
  obtain ⟨qZ, hZ, hzK⟩ := target_reindex
    (fun w : G.weylGroup => (schubertVariety G w).toOver) (flagVariety G).toOver
    (fun w => schubertInclusion G w) (simpleWeylWord_append_singleton G.rootBase word i)
    Z F z mF ρ qZl hZc hjZ
  have hroot : (word ++ [i]).get p = i := append_get_last word i
  rcases hQ (ULift.up p) with ⟨hQfp, hπfp, hπqc, hπsep, hQc, hπc⟩
  let : LocallyOfFinitePresentation (Q (ULift.up p)).hom := hQfp
  let : LocallyOfFinitePresentation (π (ULift.up p)).left := hπfp
  let : QuasiCompact (π (ULift.up p)).left := hπqc
  let : IsSeparated (π (ULift.up p)).left := hπsep
  obtain ⟨qQ, hQQ, hπQ⟩ := projection_reindex (flagVariety G).toOver
    (fun s : G.rootBase.support => (partialFlagVariety G {s}).toOver)
    (fun s => partialFlagMorphism G {s}) hroot F (Q (ULift.up p)) (π (ULift.up p)) mF ρ (mQ
      (ULift.up p)) hQc hπc
  have hnm : qNl ≫ (m ≫ z).left = bsdhMap G (word ++ [i]) ≫ mF := by
    exact (endpoint_factor qNl qZl mF m.left z.left
      (bsdhSchubertMap G (word ++ [i]) hred).left
      (schubertInclusion G (simpleWeylWord G.rootBase (word ++ [i]))).left heN hjZ).trans
      (congrArg (fun a => a ≫ mF) (bsdhSchubertMap_comp G (word ++ [i]) hred))
  have haf : qA ≫ (f ≫ j).left = bsdhMap G word ≫ mF := by
    exact (endpoint_factor qA qY mF f.left j.left
      (bsdhSchubertMap G word hred₀).left
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left
      heA' hjY').trans
      (congrArg (fun a => a ≫ mF) (bsdhSchubertMap_comp G word hred₀))
  obtain ⟨t, _ht, hprev⟩ := ih hred₀ l.val l.property.1 F
    inferInstance inferInstance inferInstance mF hFcart A Y f j inferInstance inferInstance
    qA qY hA hY heA' hjY'
    ⟨l.val, l.property.1, le_rfl⟩
  obtain ⟨a, _hta, hgc⟩ := exists_scalar_endpoint_step l.val G word
    (simpleWeylWord G.rootBase word) i (append_ascent G word i hred)
    f j m z (π (ULift.up p)) qNl qA qY qZ mF qQ
    hNc hA hY hZ hFcart hQQ
    hnm haf.symm hjY'.symm hzK hπQ t hprev
  let lA : CoefficientStage k.val :=
    ⟨a.val, a.property.1, l.property.2.trans a.property.2⟩
  let kA : CoefficientStage (PrefixEndpointData.coefficient d) :=
    ⟨a.val, a.property.1, k.property.2.trans (l.property.2.trans a.property.2)⟩
  let r : CoefficientStage S := ⟨(PrefixEndpointData.coefficient d),
    (PrefixEndpointData.finiteGeneration d), (PrefixEndpointData.original_le d)⟩
  have hg₁ := scalar_endpoint_gc k.val (chosenScalarArrow κ₁ eT) l a hgc
  have hg₂ := scalar_endpoint_gc (PrefixEndpointData.coefficient d) eT k lA hg₁
  have hg₃ := scalar_endpoint_gc S e r kA hg₂
  exact ⟨⟨a.val, a.property.1, (PrefixEndpointData.original_le d).trans kA.property.2⟩,
    (PrefixEndpointData.start_le d).trans kA.property.2, hg₃⟩


private theorem endpoint_induction {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) : wordEndpointConnected G word := by
  induction word using List.reverseRecOn with
  | nil =>
    intro hred S hS P hPfp hPqc hPsep qP _hP C D e j heProp hjProp qC qD hC hD he _hj start
    let : LocallyOfFinitePresentation P.hom := hPfp
    let : QuasiCompact P.hom := hPqc
    let : IsSeparated P.hom := hPsep
    let : IsProper e.left := heProp
    let : IsClosedImmersion j.left := hjProp
    let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
    let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
    have hprops := endpoint_properties S C D P e j
    let : LocallyOfFinitePresentation C.hom := hprops.1
    let : QuasiCompact C.hom := hprops.2.1
    let : LocallyOfFinitePresentation D.hom := hprops.2.2.1
    let : QuasiCompact D.hom := hprops.2.2.2.1
    obtain ⟨k, hk, _hiso, hgc, _hbase, _hold, _hfields⟩ :=
      exists_empty_endpoint_connected S hS G hred qC qD hC hD e he start
    exact ⟨k, hk, hgc⟩
  | append_singleton word i ih =>
    intro hred S hS P hPfp hPqc hPsep qP hP C D e j heProp hjProp qC qD hC hD he hj start
    let : LocallyOfFinitePresentation P.hom := hPfp
    let : QuasiCompact P.hom := hPqc
    let : IsSeparated P.hom := hPsep
    let : IsProper e.left := heProp
    let : IsClosedImmersion j.left := hjProp
    exact successor_from_partial G word i ih hred S P qP C D e j qC qD start
      (exists_word_partial_diagram G (word ++ [i]) hred S hS P qP hP
        C D e j qC qD hC hD he hj start)

private def RetainedComparisons {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C D P : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    (CK DK FK : Over (Spec (.of K))) (eK : CK ⟶ DK) (jK : DK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left) (qP : FK.left ⟶ P.left)
    (k : CoefficientStage S) : Prop :=
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  ∃ (qCk : CK.left ⟶ (stageScalarModel S C.hom k).left)
    (qDk : DK.left ⟶ (stageScalarModel S D.hom k).left)
    (qPk : FK.left ⟶ (stageScalarModel S P.hom k).left),
    IsPullback qCk CK.hom (stageScalarModel S C.hom k).hom ρ ∧
    IsPullback qDk DK.hom (stageScalarModel S D.hom k).hom ρ ∧
    IsPullback qPk FK.hom (stageScalarModel S P.hom k).hom ρ ∧
    qCk ≫ pullback.snd κ C.hom = qC ∧
    qDk ≫ pullback.snd κ D.hom = qD ∧
    qPk ≫ pullback.snd κ P.hom = qP ∧
    qCk ≫ (chosenScalarArrow κ e).left = eK.left ≫ qDk ∧
    qDk ≫ (chosenScalarArrow κ j).left = jK.left ≫ qPk

private theorem retained_comparisons {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C D P : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    (CK DK FK : Over (Spec (.of K))) (eK : CK ⟶ DK) (jK : DK ⟶ FK)
    (qC : CK.left ⟶ C.left) (qD : DK.left ⟶ D.left) (qP : FK.left ⟶ P.left)
    (hC : IsPullback qC CK.hom C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD DK.hom D.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hP : IsPullback qP FK.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = eK.left ≫ qD) (hj : qD ≫ j.left = jK.left ≫ qP)
    (k : CoefficientStage S) : RetainedComparisons S C D P e j CK DK FK eK jK qC qD qP k := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k.val K))
  let qCk := stage_map S C CK qC hC k
  let qDk := stage_map S D DK qD hD k
  let qPk := stage_map S P FK qP hP k
  have hCk := stage_map_cartesian S C CK qC hC k
  have hDk := stage_map_cartesian S D DK qD hD k
  have hPk := stage_map_cartesian S P FK qP hP k
  have hCo := stage_map_original S C CK qC hC k
  have hDo := stage_map_original S D DK qD hD k
  have hPo := stage_map_original S P FK qP hP k
  exact ⟨qCk, qDk, qPk, hCk, hDk, hPk, hCo, hDo, hPo,
    scalar_comparison κ ρ e eK qC qD qCk qDk hCk hDk hCo hDo he,
    scalar_comparison κ ρ j jK qD qP qDk qPk hDk hPk hDo hPo hj⟩

/-- A reduced-word endpoint becomes geometrically connected after enlarging
the coefficients of the prescribed model. The enlarged endpoint is the
scalar extension of the given arrow, and the enlargement preserves the
requested lower coefficient stage. -/
theorem exists_word_endpoint_connected {K : Type u}
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
    (hj : qD ≫ j.left =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ qP)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let ek := chosenScalarArrow κ e
      GeometricallyConnected ek.left ∧ IsProper ek.left ∧
      (ek.left ≫ (stageScalarModel S D.hom k).hom = (stageScalarModel S C.hom k).hom) ∧
      (ek.left ≫ pullback.snd κ D.hom = pullback.snd κ C.hom ≫ e.left) ∧
      (∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S D.hom k).left),
        ConnectedSpace (pullback ek.left y : Scheme.{u})) ∧
      RetainedComparisons S C D P e j (bsdhVariety G word).toOver
        (schubertVariety G (simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
        (bsdhSchubertMap G word hred) (schubertInclusion G (simpleWeylWord G.rootBase word))
        qC qD qP k := by
  obtain ⟨k, hk, hgc⟩ := endpoint_induction G word hred S hS P
    inferInstance inferInstance inferInstance qP hP C D e j inferInstance inferInstance
    qC qD hC hD he hj start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let : GeometricallyConnected (chosenScalarArrow κ e).left := hgc
  have hproper : IsProper (chosenScalarArrow κ e).left :=
    scalar_property (@IsProper) κ e inferInstance
  have hretained := retained_comparisons S C D P e j (bsdhVariety G word).toOver
    (schubertVariety G (simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
    (bsdhSchubertMap G word hred) (schubertInclusion G (simpleWeylWord G.rootBase word))
    qC qD qP hC hD hP he hj k
  exact ⟨k, hk, hgc, hproper, (chosenScalarArrow κ e).w,
    chosenScalarArrow_snd κ e, (fun L hL y =>
      @field_connected _ _ (chosenScalarArrow κ e).left hgc L hL y), hretained⟩

end SchubertGeometry
