import OrbitComplexity.SchubertGeometry.Normality.WordEndpointStage
import OrbitComplexity.SchubertGeometry.Normality.WordFaceModelComparison
import OrbitComplexity.SchubertGeometry.Normality.SchubertImageFibres
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ReducedWordFaces
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import Mathlib.Data.Set.Finite.Lattice
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # One coefficient stage for compatible Schubert images

The reduced subword faces and their arithmetic image maps are chosen before
the field and splitting. A common upper coefficient stage then retains every
Schubert image ideal for the same ambient pushforward splitting.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting
open ReductiveGroups

open private scalar_schubert_boundaries from
  OrbitComplexity.SchubertGeometry.Normality.WordEndpointStage

namespace SchubertGeometry

private theorem property_transport {I : Sort*} (P : I → Prop) {a b : I}
    (h : a = b) (ha : P a) : P b := h ▸ ha

private theorem cartesian_third_eq {C : Type u} [Category.{v} C]
    {P X Y Z : C} {f : P ⟶ X} {g : P ⟶ Y} {a a' : X ⟶ Z} {b : Y ⟶ Z}
    (h : a = a') (hp : IsPullback f g a b) : IsPullback f g a' b := by
  cases h
  exact hp

private theorem fibre_cartesian {C : Type u} [Category.{v} C]
    {X Y A B Q : C} (c : A ⟶ Y) (a : A ⟶ B) (y : Y ⟶ B) (hc : c ≫ y = a)
    (q : X ⟶ Y) (x : X ⟶ Q) (κ : Q ⟶ B) [HasPullback q c]
    (hp : IsPullback q x y κ) :
    IsPullback (pullback.snd q c) (pullback.fst q c ≫ x) a κ :=
  cartesian_third_eq hc ((IsPullback.of_hasPullback q c).flip.paste_vert hp)

private theorem coefficient_triangle {K L : Type u} [CommRing K] [CommRing L]
    (S T R : Subalgebra ℤ K) (hST : S ≤ T) (hTR : T ≤ R) (hSR : S ≤ R)
    [Algebra R L] :
    ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom).comp
        (Subalgebra.inclusion hST).toRingHom =
      (algebraMap R L).comp (Subalgebra.inclusion hSR).toRingHom := by
  ext x
  rfl

private theorem spec_triangle {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) (h : A →+* D) (hh : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom h)
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom k)) hh

/-- Every word-fibre splitting compatible with its boundary kernels has
endpoint pushforward compatible with the Schubert image ideals. -/
def wordImageFibres {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S)))
    (D : G.weylGroup → Over (Spec (.of S))) (j : ∀ x, D x ⟶ F)
    (endpoint : C ⟶ F) (boundaries : Fin word.length → Over C.left)
    (r : CoefficientStage S) : Prop :=
  ∀ (κ : Type u) [Field κ] [Algebra r.val κ]
    (W Z : Over (Spec (.of κ))) [CompactSpace W.left] [QuasiSeparatedSpace Z.left]
    (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left)
    (_hW : IsPullback qW W.hom C.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
        (Subalgebra.inclusion r.property.2).toRingHom))))
    (_hZ : IsPullback qZ Z.hom F.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
        (Subalgebra.inclusion r.property.2).toRingHom))))
    (e : W ⟶ Z) [QuasiCompact e.left] [IsIso e.left.c]
    (_he : e.left ≫ qZ = qW ≫ endpoint.left)
    (B : Fin word.length → Over W.left)
    (b : ∀ k, (B k).left ⟶ (boundaries k).left)
    (_hB : ∀ k, IsPullback (B k).hom (b k) qW (boundaries k).hom)
    (p : ℕ) (sigma : SchemeSplitting W.left p)
    (_hcompatible : ∀ k, sigma.IsCompatible (B k).hom.ker),
    ∀ x, WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase word) →
      (sigma.pushforward e.left).IsCompatible (pullback.fst qZ (j x).left).ker

/-- A single coefficient stage retains all Schubert image ideals below the
chosen reduced word. On every field fibre, one word splitting compatible with
the omitted-letter boundaries pushes forward to a splitting compatible with
every one of the original Schubert models in the same ambient flag fibre. -/
theorem exists_common_schubert_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (w : List G.rootBase.support)
    (hw : (weylCoxeterSystem G.rootBase).IsReduced w)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (M F : Over (Spec (.of S))) (D : G.weylGroup → Over (Spec (.of S)))
    [CompactSpace M.left] [QuasiSeparatedSpace M.left]
    [LocallyOfFinitePresentation M.hom] [LocallyOfFiniteType F.hom]
    [∀ x, CompactSpace (D x).left] [∀ x, QuasiSeparatedSpace (D x).left]
    [∀ x, LocallyOfFinitePresentation (D x).hom]
    (i : M ⟶ F) (j : ∀ x, D x ⟶ F)
    (hjclosed : ∀ x, IsClosedImmersion (j x).left)
    (m : bsdhScheme G w ⟶ M.left)
    (hm : IsPullback m (bsdhToSpec G w) M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qD : ∀ x, (schubertVariety G x).toOver.left ⟶ (D x).left)
    (hD : ∀ x, IsPullback (qD x) (schubertVariety G x).toOver.hom (D x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hi : bsdhMap G w ≫ qF = m ≫ i.left)
    (hj : ∀ x, (schubertInclusion G x).left ≫ qF = qD x ≫ (j x).left)
    (boundaries : Fin w.length → Over M.left)
    (hclosed : ∀ k, IsClosedImmersion (boundaries k).hom)
    (n : ∀ k, bsdhScheme G (w.eraseIdx k.val) ⟶ (boundaries k).left)
    (hn : ∀ k, IsPullback (bsdhOmitMap G w k) (n k) m (boundaries k).hom)
    (start : CoefficientStage S) :
    ∃ r : CoefficientStage S, start ≤ r ∧
      @wordImageFibres.{u} K inferInstance inferInstance inferInstance
        G w S M F D j i boundaries r := by
  let Fibre (x : G.weylGroup) (L : Type u) [Field L] (τ : S →+* L) : Prop :=
    ∀ (W Z : Over (Spec (.of L))) [CompactSpace W.left] [QuasiSeparatedSpace Z.left]
      (qW : W.left ⟶ M.left) (qZ : Z.left ⟶ F.left)
      (_hW : IsPullback qW W.hom M.hom (Spec.map (CommRingCat.ofHom τ)))
      (_hZ : IsPullback qZ Z.hom F.hom (Spec.map (CommRingCat.ofHom τ)))
      (endpoint : W ⟶ Z) [QuasiCompact endpoint.left] [IsIso endpoint.left.c]
      (_hendpoint : endpoint.left ≫ qZ = qW ≫ i.left)
      (B : Fin w.length → Over W.left)
      (b : ∀ k, (B k).left ⟶ (boundaries k).left)
      (_hB : ∀ k, IsPullback (B k).hom (b k) qW (boundaries k).hom)
      (p : ℕ) (splitting : SchemeSplitting W.left p)
      (_hcompatible : ∀ k, splitting.IsCompatible (B k).hom.ker),
      (splitting.pushforward endpoint.left).IsCompatible (pullback.fst qZ (j x).left).ker
  let P (x : G.weylGroup) (r : CoefficientStage S) : Prop :=
    ∀ (L : Type u) [Field L] [Algebra r.val L],
      Fibre x L ((algebraMap r.val L).comp (Subalgebra.inclusion r.property.2).toRingHom)
  have hmono (x : G.weylGroup) (r t : CoefficientStage S) (hrt : r ≤ t)
      (hr : P x r) : P x t := by
    intro L _ _
    let : Algebra r.val L :=
      ((algebraMap t.val L).comp (Subalgebra.inclusion hrt).toRingHom).toAlgebra
    have hτ : (algebraMap r.val L).comp (Subalgebra.inclusion r.property.2).toRingHom =
        (algebraMap t.val L).comp (Subalgebra.inclusion t.property.2).toRingHom :=
      coefficient_triangle S r.val t.val r.property.2 hrt t.property.2
    exact property_transport (Fibre x L) hτ (hr L)
  have hone (x : G.weylGroup)
      (hx : WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase w)) :
      ∃ r : CoefficientStage S, start ≤ r ∧ P x r := by
    obtain ⟨v, hv, hred, hprod, _⟩ := bsdh_bruhat_face G w hw x hx
    have hword : ∃ r : CoefficientStage S, start ≤ r ∧
        P (simpleWeylWord G.rootBase v) r := by
      obtain ⟨omitted, t, hstart, e, he, R, hR, htR, htR', hfield⟩ :=
        exists_subword_image_stage G hv hred S hS M (D (simpleWeylWord G.rootBase v)) F
          i (j (simpleWeylWord G.rootBase v)) m hm (qD (simpleWeylWord G.rootBase v))
          (hD (simpleWeylWord G.rootBase v)) qF hi (hj (simpleWeylWord G.rootBase v))
          boundaries hclosed n hn start
      let J := omitted.sup (fun k => (boundaries k).hom.ker)
      let C : Over (Spec (.of S)) := Over.mk (J.subschemeι ≫ M.hom)
      let r : CoefficientStage S := ⟨R, hR, t.property.2.trans htR⟩
      refine ⟨r, hstart.trans htR, ?_⟩
      intro L _ _ W Z _ _ qW qZ hW hZ endpoint _ _ hEndpoint B b hB p splitting hCompatible
      let σ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      let ρ := Spec.map (CommRingCat.ofHom
        ((algebraMap R L).comp (Subalgebra.inclusion htR').toRingHom))
      let κ := Spec.map (CommRingCat.ofHom
        ((algebraMap R L).comp (Subalgebra.inclusion r.property.2).toRingHom))
      have hκ : ρ ≫ σ = κ := spec_triangle (Subalgebra.inclusion t.property.2).toRingHom
        ((algebraMap R L).comp (Subalgebra.inclusion htR').toRingHom)
        ((algebraMap R L).comp (Subalgebra.inclusion r.property.2).toRingHom)
        (coefficient_triangle S t.val R t.property.2 htR' r.property.2)
      let A : Scheme.{u} := pullback qW J.subschemeι
      let Y : Scheme.{u} := pullback qZ (j (simpleWeylWord G.rootBase v)).left
      let a : A ⟶ W.left := pullback.fst qW J.subschemeι
      let qA : A ⟶ J.subscheme := pullback.snd qW J.subschemeι
      let jY : Y ⟶ Z.left := pullback.fst qZ (j (simpleWeylWord G.rootBase v)).left
      let qY : Y ⟶ (D (simpleWeylWord G.rootBase v)).left :=
        pullback.snd qZ (j (simpleWeylWord G.rootBase v)).left
      let a₀ : A ⟶ Spec (.of L) := a ≫ W.hom
      let y₀ : Y ⟶ Spec (.of L) := jY ≫ Z.hom
      have hA : IsPullback qA a₀ C.hom κ :=
        fibre_cartesian J.subschemeι C.hom M.hom rfl qW W.hom κ hW
      have hY : IsPullback qY y₀ (D (simpleWeylWord G.rootBase v)).hom κ :=
        fibre_cartesian (j (simpleWeylWord G.rootBase v)).left
          (D (simpleWeylWord G.rootBase v)).hom F.hom (j (simpleWeylWord G.rootBase v)).w
          qZ Z.hom κ hZ
      let pC := pullback.snd σ C.hom
      let pD := pullback.snd σ (D (simpleWeylWord G.rootBase v)).hom
      have hCT : IsPullback pC (stageScalarModel S C.hom t).hom C.hom σ :=
        (IsPullback.of_hasPullback σ C.hom).flip
      have hDT : IsPullback pD (stageScalarModel S (D (simpleWeylWord G.rootBase v)).hom t).hom
          (D (simpleWeylWord G.rootBase v)).hom σ :=
        (IsPullback.of_hasPullback σ (D (simpleWeylWord G.rootBase v)).hom).flip
      obtain ⟨qAT, qYT, g, hAT, hYT, _, _, hg, hgbase, hgEndpoint⟩ :=
        exists_scalar_image_factor J.subschemeι i.left (j (simpleWeylWord G.rootBase v)).left
          C.hom (D (simpleWeylWord G.rootBase v)).hom F.hom σ ρ κ hκ pC pD
          (stageScalarModel S C.hom t).hom
          (stageScalarModel S (D (simpleWeylWord G.rootBase v)).hom t).hom hCT hDT
          e.left e.w he qW qZ W.hom Z.hom hZ endpoint.left endpoint.w hEndpoint
          a jY qA qY a₀ y₀ hA hY rfl rfl pullback.condition pullback.condition
      let XL : Over (Spec (.of L)) := Over.mk a₀
      let YL : Over (Spec (.of L)) := Over.mk y₀
      let fL : XL ⟶ YL := Over.homMk g hgbase
      let : IsClosedImmersion (j (simpleWeylWord G.rootBase v)).left :=
        hjclosed (simpleWeylWord G.rootBase v)
      let : IsClosedImmersion a := by
        change IsClosedImmersion (pullback.fst qW J.subschemeι)
        infer_instance
      let : IsClosedImmersion jY := by
        change IsClosedImmersion (pullback.fst qZ (j (simpleWeylWord G.rootBase v)).left)
        infer_instance
      let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace a
      let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated jY
      let : QuasiCompact fL.left := (show QuasiCompact g from inferInstance)
      obtain ⟨_, hkernel⟩ := hfield L XL YL fL qAT qYT hAT hYT hg.symm
      exact (hkernel Z.left jY).2 W.left p splitting a qW qA
        (IsPullback.of_hasPullback qW J.subschemeι) B b hB hCompatible endpoint.left hgEndpoint.symm
    exact property_transport
      (fun y => ∃ r : CoefficientStage S, start ≤ r ∧ P y r) hprod hword
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  let I := {x : G.weylGroup // WeylBruhatLE G.rootBase x (simpleWeylWord G.rootBase w)}
  choose stages _hstart hstages using (fun x : I => hone x.val x.property)
  let : Nonempty (CoefficientStage S) := ⟨start⟩
  obtain ⟨t, ht⟩ := (Set.finite_range stages).bddAbove
  obtain ⟨r, htr, hstartr⟩ := exists_ge_ge t start
  refine ⟨r, hstartr, ?_⟩
  intro L _ _ W Z _ _ qW qZ hW hZ endpoint _ _ hEndpoint B b hB p splitting hCompatible x hx
  let xi : I := ⟨x, hx⟩
  have hxstage : P x r := hmono x (stages xi) r ((ht ⟨xi, rfl⟩).trans htr) (hstages xi)
  exact hxstage L W Z qW qZ hW hZ endpoint hEndpoint B b hB p splitting hCompatible

/-- A word model and its omitted-letter boundaries retain all Schubert
image ideals for every compatible word splitting on one coefficient stage. -/
theorem exists_prefix_schubert_stage {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word) (initial : CoefficientStage M.S)
    (C F : Over (Spec (.of initial.val)))
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal C.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion initial.property.2).toRingHom)))
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (hOriginalNative : qC ≫ qOriginal = M.m₀)
    (hw : (weylCoxeterSystem G.rootBase).IsReduced word)
    (D : G.weylGroup → Over (Spec (.of initial.val)))
    [LocallyOfFinitePresentation F.hom]
    [∀ x, CompactSpace (D x).left] [∀ x, QuasiSeparatedSpace (D x).left]
    [∀ x, LocallyOfFinitePresentation (D x).hom]
    (j : ∀ x, D x ⟶ F) (hjclosed : ∀ x, IsClosedImmersion (j x).left)
    (qD : ∀ x, (schubertVariety G x).toOver.left ⟶ (D x).left)
    (hD : ∀ x, IsPullback (qD x) (schubertVariety G x).toOver.hom (D x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (hj : ∀ x, (schubertInclusion G x).left ≫ qF = qD x ≫ (j x).left)
    (start : CoefficientStage initial.val) :
    ∃ (t : CoefficientStage initial.val), start ≤ t ∧
      let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      let MT := stageScalarModel initial.val C.hom t
      let FT := stageScalarModel initial.val F.hom t
      let DT := fun x => stageScalarModel initial.val (D x).hom t
      let jT := fun x => chosenScalarArrow τ (j x)
      let qMT := pullback.snd τ C.hom ≫ qOriginal
      let boundaries := fun k => Over.mk (pullback.fst qMT (M.boundaries k).hom)
      ∃ (endpoint : MT ⟶ FT) (m : bsdhScheme G word ⟶ MT.left)
        (q : (flagVariety G).scheme ⟶ FT.left)
        (qDT : ∀ x, (schubertVariety G x).toOver.left ⟶ (DT x).left),
        IsPullback m (bsdhToSpec G word) MT.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback q (flagVariety G).toSpec FT.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        q ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          F.hom = qF ∧
        (∀ x, IsPullback (qDT x) (schubertVariety G x).toOver.hom (DT x).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
        m ≫ qMT = M.m₀ ∧ bsdhMap G word ≫ q = m ≫ endpoint.left ∧
        (∀ x, (schubertInclusion G x).left ≫ q = qDT x ≫ (jT x).left) ∧
        ∃ (n : ∀ k, bsdhScheme G (word.eraseIdx k.val) ⟶ (boundaries k).left),
          (∀ k, IsPullback (bsdhOmitMap G word k) (n k) m (boundaries k).hom) ∧
          ∃ (r : CoefficientStage t.val),
            @wordImageFibres.{u} K kField kClosed kZero G word t.val MT FT DT jT endpoint boundaries
              r := by
  classical
  let : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) hOriginal M.proper
  let : Smooth C.hom := MorphismProperty.of_isPullback (P := @Smooth) hOriginal M.smoothModel
  let : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  let : C.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.hom]
    infer_instance
  obtain ⟨t, hstart, endpoint, m, q, hm, hq, hmProjection, hqProjection, hEndpoint⟩ :=
    @exists_prefix_endpoint_stage.{u} K kField kClosed kZero G word
      initial.val initial.property.1 C F inferInstance inferInstance inferInstance
      qC hC qF hF start
  refine ⟨t, hstart, ?_⟩
  intro τ MT FT DT jT qMT boundaries
  have hmOriginal : m ≫ qMT = M.m₀ :=
    (Category.assoc m (pullback.snd τ C.hom) qOriginal).symm.trans
      ((congrArg (fun f => f ≫ qOriginal) hmProjection).trans hOriginalNative)
  let : IsProper MT.hom := by
    change IsProper (pullback.fst τ C.hom)
    infer_instance
  let : LocallyOfFinitePresentation MT.hom := by
    change LocallyOfFinitePresentation (pullback.fst τ C.hom)
    infer_instance
  let : CompactSpace MT.left := QuasiCompact.compactSpace_of_compactSpace MT.hom
  let : MT.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from MT.hom]
    infer_instance
  let : LocallyOfFiniteType FT.hom := by
    change LocallyOfFiniteType (pullback.fst τ F.hom)
    infer_instance
  let : ∀ x, CompactSpace (DT x).left := fun x => by
    change CompactSpace (pullback τ (D x).hom : Scheme.{u})
    infer_instance
  let : ∀ x, QuasiSeparatedSpace (DT x).left := fun x => by
    change QuasiSeparatedSpace (pullback τ (D x).hom : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd τ (D x).hom)
  let : ∀ x, LocallyOfFinitePresentation (DT x).hom := fun x => by
    change LocallyOfFinitePresentation (pullback.fst τ (D x).hom)
    infer_instance
  have hClosed (x) : IsClosedImmersion (jT x).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (@chosenScalarArrow_cartesian.{u} (Spec (.of initial.val)) (Spec (.of t.val))
        τ (D x) F (j x)).flip (hjclosed x)
  refine ⟨endpoint, m, q, ?_⟩
  obtain ⟨qDT, hDT, hjT, hBoundaryClosed, n, hn⟩ :=
    @scalar_schubert_boundaries.{u} K kField kClosed kZero G word M
      initial.val C F qOriginal D j qD hD qF hj t m q hq hmOriginal hqProjection
  refine ⟨qDT, hm, hq, hqProjection, hDT, hmOriginal, hEndpoint, hjT, n, hn, ?_⟩
  obtain ⟨r, _hr, hCommon⟩ := @exists_common_schubert_stage.{u} K kField kClosed kZero
    G word hw t.val t.property.1 MT FT DT inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance endpoint jT hClosed m hm qDT hDT q hEndpoint hjT
    boundaries hBoundaryClosed n hn ⟨t.val, t.property.1, le_rfl⟩
  exact ⟨r, hCommon⟩

end SchubertGeometry
