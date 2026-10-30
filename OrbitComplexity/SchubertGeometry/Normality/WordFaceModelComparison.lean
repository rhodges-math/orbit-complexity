import OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.SubwordFaces
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryIntersections
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Canonical arithmetic models of subword faces

The finite sum of the omitted-letter boundary ideals defines the face model.
Its comparison with a Bott--Samelson subword is constructed from equality of
closed-immersion kernels. The same ideal defines its compatible field fibres.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting
open ReductiveGroups

open private closed_iso underlyingIso from
  OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoSquares
open private ker_of_pullback from
  OrbitComplexity.SchubertGeometry.Normality.Richardson.RichardsonCoordinateKernel
open private source_cartesian closed_of_cartesian from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
open private compatible_zero from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryIntersections
open private postcompose_agreement comp_base_triangle from
  OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages

namespace SchubertGeometry

private theorem closed_kernel_comparison {A B T : Scheme.{u}}
    (i : A ⟶ T) (j : B ⟶ T) [IsClosedImmersion i] [IsClosedImmersion j]
    (h : i.ker = j.ker) : ∃ E : A ≅ B, E.hom ≫ j = i := by
  let I : Over T := Over.mk i
  let J : Over T := Over.mk j
  let Z : Over T := Over.mk (𝟙 T)
  let ii : I ⟶ Z := Over.homMk i (Category.comp_id i)
  let jj : J ⟶ Z := Over.homMk j (Category.comp_id j)
  let : IsClosedImmersion ii.left := (show IsClosedImmersion i from inferInstance)
  let : IsClosedImmersion jj.left := (show IsClosedImmersion j from inferInstance)
  obtain ⟨E, hE⟩ := closed_iso ii jj h
  exact ⟨underlyingIso E, congrArg (fun k => k.left) hE⟩

private theorem comap_finsetSup {Idx : Type v} {X Y : Scheme.{u}}
    (J : Idx → Y.IdealSheafData) (m : X ⟶ Y) (F : Finset Idx) :
    (F.sup J).comap m = F.sup (fun k => (J k).comap m) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, Scheme.IdealSheafData.comap_bot]
  | @insert k F _ ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih, Finset.sup_insert]

private theorem subscheme_pullback_kernel {X Y : Scheme.{u}}
    (J : Y.IdealSheafData) (m : X ⟶ Y) :
    (pullback.fst m J.subschemeι).ker = J.comap m :=
  (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion J.subschemeι m).trans
    (congrArg (fun I => I.comap m) J.ker_subschemeι)

private theorem subscheme_cartesian_kernel {P X Y : Scheme.{u}}
    (J : Y.IdealSheafData) (a : P ⟶ X) (q : P ⟶ J.subscheme) (x : X ⟶ Y)
    (hp : IsPullback a q x J.subschemeι) : a.ker = J.comap x :=
  (ker_of_pullback J.subschemeι a q x hp).trans
    (congrArg (fun I => I.comap x) J.ker_subschemeι)

private theorem cartesian_second_eq {C : Type*} [Category C]
    {P A B T : C} {f : P ⟶ A} {g g' : P ⟶ B} {a : A ⟶ T} {b : B ⟶ T}
    (hg : g = g') (hp : IsPullback f g a b) : IsPullback f g' a b := by
  cases hg
  exact hp

private theorem face_projection_triangle {C : Type*} [Category C]
    {V P W A B : C} (e : V ⟶ P) (p : P ⟶ W) (q : P ⟶ A)
    (j : A ⟶ B) (m : W ⟶ B) (a : V ⟶ W)
    (hp : q ≫ j = p ≫ m) (he : e ≫ p = a) :
    (e ≫ q) ≫ j = a ≫ m :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => e ≫ k) hp).trans (postcompose_agreement e p a m he))

private theorem face_endpoint_triangle {C : Type*} [Category C]
    {V W A M Y Z : C} (a : V ⟶ W) (q : V ⟶ A) (j : A ⟶ M) (m : W ⟶ M)
    (epV : V ⟶ Y) (epW : W ⟶ Y) (qY : Y ⟶ Z) (epM : M ⟶ Z)
    (ha : a ≫ epW = epV) (hq : q ≫ j = a ≫ m) (hm : epW ≫ qY = m ≫ epM) :
    epV ≫ qY = q ≫ (j ≫ epM) := by
  calc
    epV ≫ qY = (a ≫ epW) ≫ qY := congrArg (fun k => k ≫ qY) ha.symm
    _ = a ≫ (epW ≫ qY) := Category.assoc _ _ _
    _ = a ≫ (m ≫ epM) := congrArg (fun k => a ≫ k) hm
    _ = (a ≫ m) ≫ epM := (Category.assoc _ _ _).symm
    _ = (q ≫ j) ≫ epM := congrArg (fun k => k ≫ epM) hq.symm
    _ = q ≫ (j ≫ epM) := Category.assoc _ _ _

/-- The canonical sum of the arithmetic boundary ideals has the prescribed
Bott--Samelson subword as its scalar fibre. The finite set of omitted positions
is chosen from the subword before any field fibre or splitting. -/
theorem exists_word_face_model {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {v w : List G.rootBase.support} (h : v.Sublist w)
    (S : Subalgebra ℤ K) (M : Over (Spec (.of S)))
    (m : bsdhScheme G w ⟶ M.left)
    (hm : IsPullback m (bsdhToSpec G w) M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (D : Fin w.length → Over M.left)
    (hD : ∀ k, IsClosedImmersion (D k).hom)
    (n : ∀ k, bsdhScheme G (w.eraseIdx k.val) ⟶ (D k).left)
    (hn : ∀ k, IsPullback (bsdhOmitMap G w k) (n k) m (D k).hom) :
    ∃ F : Finset (Fin w.length),
      let J := F.sup (fun k => (D k).hom.ker)
      ∃ (q : bsdhScheme G v ⟶ J.subscheme) (a : bsdhScheme G v ⟶ bsdhScheme G w),
        IsClosedImmersion a ∧ a ≫ bsdhMap G w = bsdhMap G v ∧
        a.ker = F.sup (fun k => (bsdhOmitMap G w k).ker) ∧
        IsPullback q (bsdhToSpec G v) (J.subschemeι ≫ M.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
        q ≫ J.subschemeι = a ≫ m := by
  obtain ⟨a, F, ha, haendpoint, haker⟩ := bsdh_subword_face G h
  let J := F.sup (fun k => (D k).hom.ker)
  let : IsClosedImmersion a := ha
  have hcomponent (k : Fin w.length) :
      (D k).hom.ker.comap m = (bsdhOmitMap G w k).ker := by
    let : IsClosedImmersion (D k).hom := hD k
    exact (ker_of_pullback (D k).hom (bsdhOmitMap G w k) (n k) m (hn k)).symm
  have hsum : J.comap m = F.sup (fun k => (bsdhOmitMap G w k).ker) :=
    (comap_finsetSup (fun k => (D k).hom.ker) m F).trans
      (Finset.sup_congr rfl (fun k _ => hcomponent k))
  have hpker : (pullback.fst m J.subschemeι).ker = a.ker :=
    (subscheme_pullback_kernel J m).trans (hsum.trans haker.symm)
  obtain ⟨E, hE⟩ := closed_kernel_comparison a (pullback.fst m J.subschemeι) hpker.symm
  let q := E.hom ≫ pullback.snd m J.subschemeι
  have hbase : a ≫ bsdhToSpec G w = bsdhToSpec G v :=
    postcompose_agreement a (bsdhMap G w) (bsdhMap G v) (flagVariety G).toSpec haendpoint
  have hEbase : E.hom ≫ (pullback.fst m J.subschemeι ≫ bsdhToSpec G w) =
      bsdhToSpec G v :=
    (postcompose_agreement E.hom (pullback.fst m J.subschemeι) a (bsdhToSpec G w) hE).trans hbase
  have htotal := (IsPullback.of_hasPullback m J.subschemeι).flip.paste_vert hm
  have hq : IsPullback q (bsdhToSpec G v) (J.subschemeι ≫ M.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) :=
    cartesian_second_eq hEbase (source_cartesian htotal E)
  refine ⟨F, q, a, ha, haendpoint, haker, hq, ?_⟩
  exact face_projection_triangle E.hom (pullback.fst m J.subschemeι)
    (pullback.snd m J.subschemeι) J.subschemeι m a pullback.condition.symm hE

/-- The canonical fibre of a finite boundary-ideal sum is compatible with the
same splitting whenever its component boundaries are compatible and Cartesian
over the arithmetic boundary family. -/
theorem wordFace_fibre_compatible {X Y : Scheme.{u}} {p n : ℕ}
    (x : X ⟶ Y) (D : Fin n → Over Y) (B : Fin n → Over X)
    (hD : ∀ k, IsClosedImmersion (D k).hom)
    (b : ∀ k, (B k).left ⟶ (D k).left)
    (hb : ∀ k, IsPullback (B k).hom (b k) x (D k).hom)
    (splitting : SchemeSplitting X p)
    (hcompatible : ∀ k, splitting.IsCompatible (B k).hom.ker)
    (F : Finset (Fin n)) :
    splitting.IsCompatible
      (pullback.fst x (F.sup (fun k => (D k).hom.ker)).subschemeι).ker := by
  have hcomponent (k : Fin n) : (D k).hom.ker.comap x = (B k).hom.ker := by
    let : IsClosedImmersion (D k).hom := hD k
    exact (ker_of_pullback (D k).hom (B k).hom (b k) x (hb k)).symm
  have hsum : (F.sup (fun k => (D k).hom.ker)).comap x =
      F.sup (fun k => (B k).hom.ker) :=
    (comap_finsetSup (fun k => (D k).hom.ker) x F).trans
      (Finset.sup_congr rfl (fun k _ => hcomponent k))
  have hkernel : (pullback.fst x (F.sup (fun k => (D k).hom.ker)).subschemeι).ker =
      F.sup (fun k => (B k).hom.ker) :=
    (subscheme_pullback_kernel _ x).trans hsum
  rw [hkernel]
  clear hkernel hsum
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using compatible_zero splitting
  | @insert k F _ ih =>
    rw [Finset.sup_insert]
    exact (hcompatible k).sup ih

/-- A reduced subword face of the prescribed arithmetic word model has the
original Schubert image ideal after one coefficient extension. Every field
fibre retains that ideal, and compatible faces give compatible Schubert ideals
for the same splitting pushed forward to the ambient scheme. -/
theorem exists_subword_image_stage {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {v w : List G.rootBase.support} (h : v.Sublist w)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced v)
    (S : Subalgebra ℤ K) (hS : S.FG) (M D F : Over (Spec (.of S)))
    [CompactSpace M.left] [QuasiSeparatedSpace M.left]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation M.hom] [LocallyOfFinitePresentation D.hom]
    [LocallyOfFiniteType F.hom] (i : M ⟶ F) (j : D ⟶ F)
    (m : bsdhScheme G w ⟶ M.left)
    (hm : IsPullback m (bsdhToSpec G w) M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qD : (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.left ⟶ D.left)
    (hDmodel : IsPullback qD
      (schubertVariety G (simpleWeylWord G.rootBase v)).toOver.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hi : bsdhMap G w ≫ qF = m ≫ i.left)
    (hj : (schubertInclusion G (simpleWeylWord G.rootBase v)).left ≫ qF = qD ≫ j.left)
    (boundaries : Fin w.length → Over M.left)
    (hclosed : ∀ k, IsClosedImmersion (boundaries k).hom)
    (n : ∀ k, bsdhScheme G (w.eraseIdx k.val) ⟶ (boundaries k).left)
    (hn : ∀ k, IsPullback (bsdhOmitMap G w k) (n k) m (boundaries k).hom)
    (start : CoefficientStage S) :
    ∃ omitted : Finset (Fin w.length),
      let J := omitted.sup (fun k => (boundaries k).hom.ker)
      let C : Over (Spec (.of S)) := Over.mk (J.subschemeι ≫ M.hom)
      ∃ (t : CoefficientStage S) (_ : start ≤ t)
        (e : stageScalarModel S C.hom t ⟶ stageScalarModel S D.hom t),
        e.left ≫ pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
            D.hom ≫ j.left =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
            C.hom ≫ J.subschemeι ≫ i.left ∧
        ∃ R : Subalgebra ℤ K, R.FG ∧ t.val ≤ R ∧ ∃ hTR : t.val ≤ R,
          ∀ (L : Type u) [Field L] [Algebra R L]
            (XL YL : Over (Spec (.of L))) (fL : XL ⟶ YL) [QuasiCompact fL.left]
            (qXL : XL.left ⟶ (stageScalarModel S C.hom t).left)
            (qYL : YL.left ⟶ (stageScalarModel S D.hom t).left)
            (_hXL : IsPullback qXL XL.hom (stageScalarModel S C.hom t).hom
              (Spec.map (CommRingCat.ofHom
                ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))))
            (_hYL : IsPullback qYL YL.hom (stageScalarModel S D.hom t).hom
              (Spec.map (CommRingCat.ofHom
                ((algebraMap R L).comp (Subalgebra.inclusion hTR).toRingHom))))
            (_hfL : fL.left ≫ qYL = qXL ≫ e.left),
            IsSchemeTheoreticallyDominant fL.left ∧
            ∀ (Z : Scheme.{u}) (jL : YL.left ⟶ Z),
              (fL.left ≫ jL).ker = jL.ker ∧
              ∀ (W : Scheme.{u}) (p : ℕ) (splitting : SchemeSplitting W p)
                (a : XL.left ⟶ W) (x : W ⟶ M.left) (q : XL.left ⟶ J.subscheme)
                (_hface : IsPullback a q x J.subschemeι)
                (B : Fin w.length → Over W)
                (b : ∀ k, (B k).left ⟶ (boundaries k).left)
                (_hB : ∀ k, IsPullback (B k).hom (b k) x (boundaries k).hom)
                (_hcompatible : ∀ k, splitting.IsCompatible (B k).hom.ker)
                (endpoint : W ⟶ Z) [QuasiCompact endpoint] [IsIso endpoint.c]
                (_hendpoint : a ≫ endpoint = fL.left ≫ jL),
                (splitting.pushforward endpoint).IsCompatible jL.ker := by
  obtain ⟨omitted, q, a, _, haendpoint, _, hqmodel, hq⟩ :=
    exists_word_face_model G h S M m hm boundaries hclosed n hn
  let J := omitted.sup (fun k => (boundaries k).hom.ker)
  let C : Over (Spec (.of S)) := Over.mk (J.subschemeι ≫ M.hom)
  let iC : C ⟶ F := Over.homMk (J.subschemeι ≫ i.left)
    (comp_base_triangle J.subschemeι i.left M.hom F.hom i.w)
  let : IsNoetherianRing S := isNoetherianRing_of_fg hS
  let : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  let : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  let : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated J.subschemeι
  let : LocallyOfFinitePresentation C.hom := by
    change LocallyOfFinitePresentation (J.subschemeι ≫ M.hom)
    infer_instance
  have hiC : bsdhMap G v ≫ qF = q ≫ iC.left :=
    face_endpoint_triangle a q J.subschemeι m (bsdhMap G v) (bsdhMap G w)
      qF i.left haendpoint hq hi
  obtain ⟨t, hstart, e, he, hrest⟩ := exists_word_image_kernel_stage G v hred S hS
    C D F iC j q qD qF hqmodel hDmodel hiC hj start
  refine ⟨omitted, t, hstart, e, he, ?_⟩
  obtain ⟨R, hR, hTR, hTR', hfield⟩ := hrest
  refine ⟨R, hR, hTR, hTR', ?_⟩
  intro L _ _ XL YL fL _ qXL qYL hXL hYL hfL
  obtain ⟨hdominant, hkernel⟩ := hfield L XL YL fL qXL qYL hXL hYL hfL
  refine ⟨hdominant, ?_⟩
  intro Z jL
  refine ⟨(hkernel Z jL).1, ?_⟩
  intro W p splitting a x q hface B b hB hcompatible endpoint _ _ hendpoint
  let : IsClosedImmersion a := closed_of_cartesian a q x J.subschemeι hface
  have haKernel : a.ker = J.comap x := subscheme_cartesian_kernel J a q x hface
  have hcomp := wordFace_fibre_compatible x boundaries B hclosed b hB splitting hcompatible omitted
  have hcanonical : (pullback.fst x J.subschemeι).ker = J.comap x :=
    subscheme_pullback_kernel J x
  rw [hcanonical] at hcomp
  have haCompatible : splitting.IsCompatible a.ker := by
    rw [haKernel]
    exact hcomp
  exact (hkernel Z jL).2 W p splitting a endpoint hendpoint haCompatible

end SchubertGeometry
