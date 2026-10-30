import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendWeylDispatch
import OrbitComplexity.SchubertGeometry.Connectedness.AppendFibreModels
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCurveStage
import OrbitComplexity.SchubertGeometry.Connectedness.EndpointInduction
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

set_option autoImplicit false

/-! # Arithmetic connectedness of append Weyl fibres

The preceding endpoint supplies the induction hypothesis. The finite
positive-root intersections and the append incidence diagram produce
connected fibres of the same chosen endpoint after coefficient extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u v
private theorem bind_witness {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem coefficient_naturality
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {XK YK : Over (Spec (.of K))} {X Y : Over (Spec (.of S))}
    (fK : XK ⟶ YK) (f : X ⟶ Y) (qX : XK.left ⟶ X.left) (qY : YK.left ⟶ Y.left)
    (hcomm : qX ≫ f.left = fK.left ≫ qY) (k : CoefficientStage S)
    (qXk : XK.left ⟶ (stageScalarModel S X.hom k).left)
    (qYk : YK.left ⟶ (stageScalarModel S Y.hom k).left)
    (hXk : IsPullback qXk XK.hom (stageScalarModel S X.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))))
    (hYk : IsPullback qYk YK.hom (stageScalarModel S Y.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))))
    (hXo : qXk ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom = qX)
    (hYo : qYk ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) Y.hom = qY) :
    qXk ≫ (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) f).left =
      fK.left ≫ qYk := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  exact modelStageMap_eq_of_projections fK.left f.left qX qY XK.hom YK.hom qXk qYk
    (pullback.snd κ X.hom) (pullback.snd κ Y.hom)
    (stageScalarModel S X.hom k).hom (stageScalarModel S Y.hom k).hom Y.hom κ
    (IsPullback.of_hasPullback κ Y.hom).flip (chosenScalarArrow κ f).left
    (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) hXo hYo
    (chosenScalarArrow_snd κ f) (chosenScalarArrow κ f).w hXk.w hYk.w fK.w hcomm

private theorem replace_last {T : Type*} [Category T] {A B C : T}
    (f : A ⟶ B) {g g' : B ⟶ C} {a : A ⟶ C}
    (h : a = f ≫ g) (hg : g = g') : a = f ≫ g' :=
  h.trans (congrArg (fun k => f ≫ k) hg)

private theorem scalar_fp {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B)
    [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation ((scalarFunctor κ).obj X).hom := by
  change LocallyOfFinitePresentation (pullback.fst κ X.hom)
  infer_instance

private theorem scalar_qc {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B)
    [QuasiCompact X.hom] : QuasiCompact ((scalarFunctor κ).obj X).hom := by
  change QuasiCompact (pullback.fst κ X.hom)
  infer_instance

private theorem scalar_closed {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedImmersion (chosenScalarArrow κ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (scalarArrow_cartesian κ f).flip inferInstance

private theorem stage_model_properties
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (X : Over (Spec (.of S)))
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] (k : CoefficientStage S) :
    LocallyOfFinitePresentation (stageScalarModel S X.hom k).hom ∧
      CompactSpace (stageScalarModel S X.hom k).left ∧
      QuasiSeparatedSpace (stageScalarModel S X.hom k).left := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let : LocallyOfFinitePresentation (stageScalarModel S X.hom k).hom := scalar_fp κ X
  let : QuasiCompact (stageScalarModel S X.hom k).hom := scalar_qc κ X
  let : Algebra.FiniteType ℤ k.val := (Subalgebra.fg_iff_finiteType k.val).mp k.property.1
  let : IsNoetherianRing k.val := Algebra.FiniteType.isNoetherianRing ℤ k.val
  let : IsLocallyNoetherian (stageScalarModel S X.hom k).left :=
    LocallyOfFiniteType.isLocallyNoetherian (stageScalarModel S X.hom k).hom
  exact ⟨inferInstance, QuasiCompact.compactSpace_of_compactSpace
    (stageScalarModel S X.hom k).hom, inferInstance⟩

private theorem bind_append_data {A : Type*} {P : A → Prop} {B : A → Type*}
    {H : ∀ a, B a → Prop} {Q : ∀ a b, H a b → Prop} {R : Prop}
    (h : ∃ a, P a ∧ ∃ (b : B a) (hb : H a b), Q a b hb)
    (next : ∀ a, P a → ∀ b hb, Q a b hb → R) : R := by
  obtain ⟨a, ha, b, hb, hq⟩ := h
  exact next a ha b hb hq

private theorem bind_stage_four {I : Type*} [Preorder I]
    {A B C D : I → Type*} {P : ∀ i, A i → B i → C i → D i → Prop} {R : Prop}
    (start : I)
    (h : ∃ (i : I) (_ : start ≤ i) (a : A i) (b : B i) (c : C i) (d : D i),
      P i a b c d)
    (next : ∀ (i : I) (_ : start ≤ i) (a : A i) (b : B i) (c : C i) (d : D i),
      P i a b c d → R) : R := by
  obtain ⟨i, hi, a, b, c, d, hp⟩ := h
  exact next i hi a b c d hp

private def original_connected_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {NK FK : Over (Spec (.of K))} {N F : Over (Spec (.of S))}
    (nK : NK ⟶ FK) (n : N ⟶ F)
    (p : ∀ _r : J, Over.mk (𝟙 (Spec (.of K))) ⟶ FK)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qN : NK.left ⟶ N.left) (start : CoefficientStage S) : Prop :=
  ∃ q : ∀ r, (fibreModel nK (p r)).left ⟶ (fibreModel n (b r)).left,
    (∀ r, IsPullback (q r) (fibreModel nK (p r)).hom (fibreModel n (b r)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) ∧
    (∀ r, q r ≫ (fibreProjection n (b r)).left =
      (fibreProjection nK (p r)).left ≫ qN) ∧
    (∀ r, q r ≫ (fibreModel n (b r)).hom =
      (fibreModel nK (p r)).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
    ∃ (s : CoefficientStage S) (_ : start ≤ s)
      (qK : ∀ r, (fibreModel nK (p r)).left ⟶
        (stageScalarModel S (fibreModel n (b r)).hom s).left),
      (∀ r, IsPullback (qK r) (fibreModel nK (p r)).hom
        (stageScalarModel S (fibreModel n (b r)).hom s).hom
        (Spec.map (CommRingCat.ofHom (algebraMap s.val K)))) ∧
      (∀ r, qK r ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion s.property.2).toRingHom))
          (fibreModel n (b r)).hom = q r) ∧
      ∀ r, GeometricallyConnected (stageScalarModel S (fibreModel n (b r)).hom s).hom ∧
        ∀ (L : Type u) [Field L] (ρ : s.val →+* L),
          ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
            (stageScalarModel S (fibreModel n (b r)).hom s).hom : Scheme.{u})

private theorem lift_append_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {NK FK : Over (Spec (.of K))} {N F : Over (Spec (.of S))}
    (nK : NK ⟶ FK) (n : N ⟶ F)
    (p : ∀ _r : J, Over.mk (𝟙 (Spec (.of K))) ⟶ FK)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qN : NK.left ⟶ N.left)
    (q : ∀ r, (fibreModel nK (p r)).left ⟶ (fibreModel n (b r)).left)
    (h : ∀ r, IsPullback (q r) (fibreModel nK (p r)).hom (fibreModel n (b r)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hq : ∀ r, q r ≫ (fibreProjection n (b r)).left =
      (fibreProjection nK (p r)).left ≫ qN)
    (hb : ∀ r, q r ≫ (fibreModel n (b r)).hom =
      (fibreModel nK (p r)).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (start k : CoefficientStage S) (hk : start ≤ k)
    (hstage : appendStageResult k.val
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) n)
      (fun r => scalarPoint
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (b r))
      ⟨k.val, k.property.1, le_rfl⟩) :
    original_connected_result S nK n p b qN start := by
  obtain ⟨m, _hm, hGC⟩ := hstage
  let s : CoefficientStage S := ⟨m.val, m.property.1, le_trans k.property.2 m.property.2⟩
  have hks : k ≤ s := m.property.2
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let ζ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)
  let μ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion s.property.2).toRingHom)
  have hζκ : ζ ≫ κ = μ := appendModel_spec_triangle
    (Subalgebra.inclusion k.property.2).toRingHom
    (Subalgebra.inclusion m.property.2).toRingHom
    (Subalgebra.inclusion s.property.2).toRingHom rfl
  have hdirect (r : J) :
      GeometricallyConnected (stageScalarModel S (fibreModel n (b r)).hom s).hom := by
    let X := fibreModel n (b r)
    let E := (scalarFunctor ζ).mapIso (pointScalarIso κ n (b r))
    have hnested : GeometricallyConnected
        ((scalarFunctor ζ).obj ((scalarFunctor κ).obj X)).hom :=
      appendModel_iso_connected E (hGC r).1
    let T := scalarTowerIso ζ κ X ≪≫ scalarMapEq hζκ X
    exact appendModel_iso_connected T.symm hnested
  let qK := fun r => modelStageMap S (fibreModel n (b r)).hom
    (fibreModel nK (p r)).hom (q r) (h r) s
  refine ⟨q, h, hq, hb, s, le_trans hk hks, qK,
    fun r => modelStageMap_cartesian S _ _ (q r) (h r) s,
    fun r => modelStageMap_projection S _ _ (q r) (h r) s, fun r => ⟨hdirect r, ?_⟩⟩
  let : GeometricallyConnected (stageScalarModel S (fibreModel n (b r)).hom s).hom :=
    hdirect r
  exact appendModel_field_connected _

private theorem choose_family {J : Type*} {A : J → Type*}
    (P : ∀ r, A r → Prop) (h : ∀ r, ∃ a, P r a) :
    ∃ a : ∀ r, A r, ∀ r, P r (a r) := by
  classical
  exact ⟨fun r => Classical.choose (h r), fun r => Classical.choose_spec (h r)⟩

private theorem retain_original_append
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {NK FK : Over (Spec (.of K))} {N F : Over (Spec (.of S))}
    (nK : NK ⟶ FK) (n : N ⟶ F)
    (p : ∀ _r : J, Over.mk (𝟙 (Spec (.of K))) ⟶ FK)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qN : NK.left ⟶ N.left) (start k : CoefficientStage S) (hk : start ≤ k)
    (hstage : appendStageResult k.val
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) n)
      (fun r => scalarPoint
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (b r))
      ⟨k.val, k.property.1, le_rfl⟩)
    (raw : ∀ r, ∃ q : (fibreModel nK (p r)).left ⟶ (fibreModel n (b r)).left,
      IsPullback q (fibreModel nK (p r)).hom (fibreModel n (b r)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
      q ≫ (fibreProjection n (b r)).left = (fibreProjection nK (p r)).left ≫ qN ∧
      q ≫ (fibreModel n (b r)).hom =
        (fibreModel nK (p r)).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) :
    original_connected_result S nK n p b qN start := by
  apply bind_witness (choose_family _ raw)
  intro q hq
  exact lift_append_result S nK n p b qN q (fun r => (hq r).1)
    (fun r => (hq r).2.1) (fun r => (hq r).2.2) start k hk hstage

private def word_endpoint
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (bsdhMap G word) rfl

private def weyl_endpoint_point
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (x : G.weylGroup) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ (flagVariety G).toOver :=
  Over.homMk (weylFlagPoint G x).val (weylFlagPoint G x).property

/-- The finite Weyl-section fibres of the specified appended endpoint are
geometrically connected after one coefficient extension, with both original projections. -/
theorem exists_append_weyl_connected
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    {J : Type v} [Fintype J] (x : J → G.weylGroup)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (hx : ∀ r, WeylBruhatLE G.rootBase (x r)
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    {N A Y F Q : Over (Spec (.of S))}
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom]
    [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left] [GeometricallyConnected f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left] (n : N ⟶ F) (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ n.left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (hb : ∀ r, (weylFlagPoint G (x r)).val ≫ qF =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ (b r).left)
    (start : CoefficientStage S) :
    original_connected_result S (word_endpoint G (word ++ [i])) n
      (fun r => weyl_endpoint_point G (x r)) b qN start := by
  apply bind_append_data
    (exists_append_weyl_curves S hS G v i x hv hx F Q π qF qQ hF hπ b hb start)
  intro r hr _qRaw _hRaw hraw
  apply bind_stage_four start hraw.2.2
  intro k hk _E₀ E qC qFk hret
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let Nk : Over (Spec (.of k.val)) := stageScalarModel S N.hom k
  let Ak : Over (Spec (.of k.val)) := stageScalarModel S A.hom k
  let Yk : Over (Spec (.of k.val)) := stageScalarModel S Y.hom k
  let Fk : Over (Spec (.of k.val)) := stageScalarModel S F.hom k
  let Qk : Over (Spec (.of k.val)) := stageScalarModel S Q.hom k
  let fk : Ak ⟶ Yk := chosenScalarArrow κ f
  let jk : Yk ⟶ Fk := chosenScalarArrow κ j
  let nk : Nk ⟶ Fk := chosenScalarArrow κ n
  let πk : Fk ⟶ Qk := chosenScalarArrow κ π
  let bk := fun t => scalarPoint κ (b t)
  let C := fun t => stageScalarModel S (fibreModel π (b t ≫ π)).hom k
  let c := fun t => chosenScalarArrow κ (fibreProjection π (b t ≫ π))
  let hNP := stage_model_properties S N k
  let hAP := stage_model_properties S A k
  let hFP := stage_model_properties S F k
  let : LocallyOfFinitePresentation Nk.hom := hNP.1
  let : CompactSpace Nk.left := hNP.2.1
  let : QuasiSeparatedSpace Nk.left := hNP.2.2
  let : LocallyOfFinitePresentation Ak.hom := hAP.1
  let : CompactSpace Ak.left := hAP.2.1
  let : LocallyOfFinitePresentation Fk.hom := hFP.1
  let : CompactSpace Fk.left := hFP.2.1
  let : LocallyOfFinitePresentation Qk.hom := scalar_fp κ Q
  let : IsProper fk.left := appendModel_arrow_proper κ f
  let : GeometricallyConnected fk.left := appendModel_arrow_connected κ f
  let : IsClosedImmersion jk.left := scalar_closed κ j
  let qNk := modelStageMap S N.hom (bsdhToSpec G (word ++ [i])) qN hN k
  let qAk := modelStageMap S A.hom (bsdhToSpec G word) qA hA k
  let qYk := modelStageMap S Y.hom (schubertVariety G v).toSpec qY hY k
  let qQk := modelStageMap S Q.hom (partialFlagVariety G {i}).toSpec qQ hQ k
  have hNk : IsPullback qNk (bsdhToSpec G (word ++ [i])) Nk.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    modelStageMap_cartesian S N.hom _ qN hN k
  have hAk : IsPullback qAk (bsdhToSpec G word) Ak.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    modelStageMap_cartesian S A.hom _ qA hA k
  have hYk : IsPullback qYk (schubertVariety G v).toSpec Yk.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    modelStageMap_cartesian S Y.hom _ qY hY k
  have hQk : IsPullback qQk (partialFlagVariety G {i}).toSpec Qk.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    modelStageMap_cartesian S Q.hom _ qQ hQ k
  have hFk : IsPullback qFk (flagVariety G).toSpec Fk.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) := hret.2.2.2.2.1
  have hFo : qFk ≫ pullback.snd κ F.hom = qF := hret.2.2.2.2.2.2.1
  have hnk : qNk ≫ nk.left = bsdhMap G (word ++ [i]) ≫ qFk :=
    coefficient_naturality S (word_endpoint G (word ++ [i])) n qN qF hn k
      qNk qFk hNk hFk (modelStageMap_projection S N.hom _ qN hN k) hFo
  have hak : bsdhMap G word ≫ qFk = qAk ≫ (fk ≫ jk).left :=
    replace_last qAk
      (coefficient_naturality S (word_endpoint G word) (f ≫ j) qA qF ha.symm k
        qAk qFk hAk hFk (modelStageMap_projection S A.hom _ qA hA k) hFo).symm
      (congrArg Over.Hom.left (appendModel_composition κ f j))
  have hjk : (schubertInclusion G v).left ≫ qFk = qYk ≫ jk.left :=
    (coefficient_naturality S (schubertInclusion G v) j qY qF hj.symm k
      qYk qFk hYk hFk (modelStageMap_projection S Y.hom _ qY hY k) hFo).symm
  have hπk : (partialFlagMorphism G {i}).left ≫ qQk = qFk ≫ πk.left :=
    (coefficient_naturality S (partialFlagMorphism G {i}) π qF qQ hπ.w.symm k
      qFk qQk hFk hQk hFo (modelStageMap_projection S Q.hom _ qQ hQ k)).symm
  have hck (t : J) : IsPullback (c t).left (C t).hom πk.left (bk t ≫ πk).left :=
    appendModel_curve_base (hret.2.2.2.2.2.2.2.2.2 t) (appendModel_section_naturality κ π (b t))
  let startk : CoefficientStage k.val := ⟨k.val, k.property.1, le_rfl⟩
  have hstage : appendStageResult k.val nk bk startk :=
    append_from_primitive_curves k.val k.property.1 G word v i r hr.1 hr.2.1
      fk jk nk πk bk C E c hck qNk qAk qYk qFk qQk qC
      hNk hAk hYk hFk hQk hret.2.2.2.1 hnk hak hjk hπk
      hret.2.2.2.2.2.2.2.2.1 hret.2.2.2.2.2.2.2.1 startk
  apply retain_original_append S (word_endpoint G (word ++ [i])) n
    (fun t => weyl_endpoint_point G (x t)) b qN start k hk hstage
  intro t
  exact appendModel_point_comparison (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (word_endpoint G (word ++ [i])) n (weyl_endpoint_point G (x t)) (b t)
    qN qF hN hF hn.symm (hb t)

-- GAP: C6-STAGE. Apply the retained cell-product comparisons and the specified
-- Schubert cell cover to these Weyl fibres, then iterate on the word and
-- transport the resulting endpoint to the specified paired source.

end SchubertGeometry
