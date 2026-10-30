import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.TensorProduct.Maps

/-! # coefficient pullbacks and their chart comparisons

The scheme is replaced only by its specified coefficient pullback. Every
original chart is pulled back with both projection equations retained; no
properness hypothesis on the source model is needed. Overlap graphs compare
separation on an open cover after scalar extension.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

noncomputable section

universe u

private theorem chart_scalar_square {W Y YK YR : Scheme.{u}}
    (a : W ⟶ Y) (qK : YK ⟶ Y) (qR : YR ⟶ Y) (m : YK ⟶ YR)
    (hm : m ≫ qR = qK) :
    ∃ d : pullback a qK ⟶ pullback a qR,
      d ≫ pullback.fst a qR = pullback.fst a qK ∧
      d ≫ pullback.snd a qR = pullback.snd a qK ≫ m ∧
      IsPullback d (pullback.snd a qK) (pullback.snd a qR) m := by
  let d := pullback.map a qK a qR (𝟙 _) m (𝟙 _)
    (by simp) (by simpa using hm.symm)
  have hf : d ≫ pullback.fst a qR = pullback.fst a qK := by simp [d]
  have hs : d ≫ pullback.snd a qR = pullback.snd a qK ≫ m := by simp [d]
  have houter : IsPullback (d ≫ pullback.fst a qR) (pullback.snd a qK) a
      (m ≫ qR) := by
    rw [hf, hm]
    exact IsPullback.of_hasPullback a qK
  exact ⟨d, hf, hs, houter.of_right hs (IsPullback.of_hasPullback a qR)⟩

/-- A coefficient extension of the given model has the original scalar
comparison and the pullbacks of every original chart, with both legs
retained. No geometric property of the source is as a premise. -/
theorem model_scalar_extension {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {Y YK : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    ∃ m : YK ⟶ YR,
      IsPullback m baseK baseR kr ∧ m ≫ qR = qY ∧ m ≫ baseR = baseK ≫ kr ∧
      ∀ (W : Scheme.{u}) (a : W ⟶ Y),
        ∃ d : pullback a qY ⟶ pullback a qR,
          d ≫ pullback.fst a qR = pullback.fst a qY ∧
          d ≫ pullback.snd a qR = pullback.snd a qY ≫ m ∧
          IsPullback d (pullback.snd a qY ≫ baseK) (pullback.snd a qR ≫ baseR) kr := by
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hcoeff : kr ≫ sr = Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have houter : IsPullback qY baseK base (kr ≫ sr) := by rw [hcoeff]; exact h
  let t := IsPullback.of_hasPullback base sr
  let m := t.lift qY (baseK ≫ kr) (by simpa only [Category.assoc] using houter.w)
  have hm : m ≫ pullback.fst base sr = qY := t.lift_fst _ _ _
  have hb : m ≫ pullback.snd base sr = baseK ≫ kr := t.lift_snd _ _ _
  have hcart : IsPullback m baseK (pullback.snd base sr) kr :=
    IsPullback.of_right' houter t
  refine ⟨m, hcart, hm, hb, ?_⟩
  intro W a
  obtain ⟨d, hf, hs, hd⟩ := chart_scalar_square a qY (pullback.fst base sr) m hm
  exact ⟨d, hf, hs, hd.paste_vert hcart⟩

set_option autoImplicit false

/-- The two projections of an overlap map to the chart product over a base. -/
def coverOverlapGraph {X S : Scheme.{u}} (U : X.OpenCover.{u}) (s : X ⟶ S)
    (i j : U.I₀) :
    pullback (U.f i) (U.f j) ⟶ pullback (U.f i ≫ s) (U.f j ≫ s) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    (by rw [← Category.assoc, pullback.condition, Category.assoc])

/-- The first projection of an overlap graph is the first overlap projection. -/
theorem coverOverlapGraph_fst {X S : Scheme.{u}} (U : X.OpenCover.{u}) (s : X ⟶ S)
    (i j : U.I₀) :
    coverOverlapGraph U s i j ≫ pullback.fst _ _ = pullback.fst (U.f i) (U.f j) :=
  pullback.lift_fst _ _ _

/-- The second projection of an overlap graph is the second overlap projection. -/
private theorem coverOverlapGraph_snd {X S : Scheme.{u}} (U : X.OpenCover.{u}) (s : X ⟶ S)
    (i j : U.I₀) :
    coverOverlapGraph U s i j ≫ pullback.snd _ _ = pullback.snd (U.f i) (U.f j) :=
  pullback.lift_snd _ _ _

/-- Closed overlap graphs on an open cover give a separated structure morphism. -/
private theorem separated_of_cover_graphs {X S : Scheme.{u}}
    (U : X.OpenCover.{u}) (s : X ⟶ S)
    (h : ∀ i j, IsClosedImmersion (coverOverlapGraph U s i j)) : IsSeparated s := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight U U s s)
  rintro ⟨i, j⟩
  change IsClosedImmersion (pullback.snd (pullback.diagonal s)
    (pullback.map (U.f i ≫ s) (U.f j ≫ s) s s
      (U.f i) (U.f j) (𝟙 S) (by simp) (by simp)))
  have he : coverOverlapGraph U s i j = pullback.mapDesc (U.f i) (U.f j) s := by
    apply pullback.hom_ext <;> simp [coverOverlapGraph, pullback.mapDesc, pullback.map]
  let : IsClosedImmersion (pullback.mapDesc (U.f i) (U.f j) s) := he ▸ h i j
  let hsquare := pullback_map_diagonal_isPullback (U.f i) (U.f j) s
  rw [← hsquare.isoPullback_inv_snd]
  infer_instance

private theorem overlap_square
    {A C X B T AT CT XT : Scheme.{u}}
    (f : A ⟶ X) (g : C ⟶ X) (s : X ⟶ B) (κ : T ⟶ B)
    (fT : AT ⟶ XT) (gT : CT ⟶ XT)
    (qA : AT ⟶ A) (qC : CT ⟶ C) (qX : XT ⟶ X)
    (tA : AT ⟶ T) (tC : CT ⟶ T) (tX : XT ⟶ T)
    (hA : IsPullback qA tA (f ≫ s) κ)
    (hC : IsPullback qC tC (g ≫ s) κ)
    (hX : IsPullback qX tX s κ)
    (hf : fT ≫ qX = qA ≫ f) (hg : gT ≫ qX = qC ≫ g)
    (htf : fT ≫ tX = tA) (htg : gT ≫ tX = tC) :
    IsPullback
      (pullback.map fT gT f g qA qC qX hf hg)
      (pullback.fst fT gT ≫ tA)
      (pullback.fst f g ≫ f ≫ s) κ := by
  let q := pullback.map fT gT f g qA qC qX hf hg
  have hqf : q ≫ pullback.fst f g = pullback.fst fT gT ≫ qA := by
    simp [q, pullback.map]
  have hqg : q ≫ pullback.snd f g = pullback.snd fT gT ≫ qC := by
    simp [q, pullback.map]
  have ht : pullback.fst fT gT ≫ tA = pullback.snd fT gT ≫ tC := by
    rw [← htf, ← htg, ← Category.assoc, pullback.condition, Category.assoc]
  change IsPullback q _ _ _
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, hqf]
    simpa only [Category.assoc] using congrArg
      (fun a => pullback.fst fT gT ≫ a) hA.w
  · intro Z a b hq ht'
    apply pullback.hom_ext
    · apply hA.hom_ext
      · have h := congrArg (fun z => z ≫ pullback.fst f g) hq
        simpa only [Category.assoc, hqf] using h
      · exact ht'
    · apply hC.hom_ext
      · have h := congrArg (fun z => z ≫ pullback.snd f g) hq
        simpa only [Category.assoc, hqg] using h
      · simpa only [Category.assoc, ← ht] using ht'
  · intro Z a b hab
    have ha : (a ≫ pullback.fst f g) ≫ (f ≫ s) = b ≫ κ := by
      simpa only [Category.assoc] using hab
    have hc : (a ≫ pullback.snd f g) ≫ (g ≫ s) = b ≫ κ := by
      calc
        (a ≫ pullback.snd f g) ≫ (g ≫ s) =
            a ≫ pullback.fst f g ≫ f ≫ s := by
          exact (congrArg (fun z => a ≫ z ≫ s)
            (pullback.condition (f := f) (g := g)).symm)
        _ = b ≫ κ := hab
    let aT := hA.lift (a ≫ pullback.fst f g) b ha
    let cT := hC.lift (a ≫ pullback.snd f g) b hc
    have hac : aT ≫ fT = cT ≫ gT := by
      apply hX.hom_ext
      · calc
          (aT ≫ fT) ≫ qX = aT ≫ qA ≫ f := by rw [Category.assoc, hf]
          _ = a ≫ pullback.fst f g ≫ f := by simp [aT]
          _ = a ≫ pullback.snd f g ≫ g :=
            congrArg (fun z => a ≫ z) (pullback.condition (f := f) (g := g))
          _ = (cT ≫ gT) ≫ qX := by rw [Category.assoc, hg]; simp [cT]
      · simp [Category.assoc, htf, htg, aT, cT]
    refine ⟨pullback.lift aT cT hac, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, hqf, pullback.lift_fst_assoc, aT,
          IsPullback.lift_fst]
      · simp only [Category.assoc, hqg, pullback.lift_snd_assoc, cT,
          IsPullback.lift_fst]
    · simp [aT]

private theorem chart_square {B T X : Scheme.{u}} (κ : T ⟶ B) (s : X ⟶ B)
    {A : Scheme.{u}} (f : A ⟶ X) :
    IsPullback (pullback.snd (pullback.snd κ s) f)
      (pullback.fst (pullback.snd κ s) f ≫ pullback.fst κ s) (f ≫ s) κ :=
  (IsPullback.of_hasPullback (pullback.snd κ s) f).flip.paste_vert
    (IsPullback.of_hasPullback κ s).flip

private theorem scalar_overlap_square {B T X : Scheme.{u}}
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u}) (i j : U.I₀) :
    let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
    IsPullback
      (pullback.map (V.f i) (V.f j) (U.f i) (U.f j)
        (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) (pullback.snd κ s)
        pullback.condition pullback.condition)
      (pullback.fst (V.f i) (V.f j) ≫ V.f i ≫ pullback.fst κ s)
      (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) κ := by
  exact overlap_square (U.f i) (U.f j) s κ
    (pullback.fst _ (U.f i)) (pullback.fst _ (U.f j))
    (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) (pullback.snd κ s)
    _ _ (pullback.fst κ s) (chart_square κ s (U.f i))
    (chart_square κ s (U.f j)) (IsPullback.of_hasPullback κ s).flip
    pullback.condition pullback.condition rfl rfl

/-- The overlap of the pulled back cover is the scalar extension of the
corresponding overlap, with its structure map to the base. -/
def scalarCoverOverlapIso {B T X : Scheme.{u}} (κ : T ⟶ B) (s : X ⟶ B)
    (U : X.OpenCover.{u}) (i j : U.I₀) :
    let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
    pullback (V.f i) (V.f j) ≅
      pullback κ (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) :=
  (scalar_overlap_square κ s U i j).flip.isoPullback

/-- Scalar extension commutes with products of charts over the base. -/
theorem scalar_product_square {B T X : Scheme.{u}}
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u}) (i j : U.I₀) :
    let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
    let t : pullback κ s ⟶ T := pullback.fst κ s
    IsPullback
      (pullback.map (V.f i ≫ t) (V.f j ≫ t) (U.f i ≫ s) (U.f j ≫ s)
        (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) κ
        (chart_square κ s (U.f i)).w.symm
        (chart_square κ s (U.f j)).w.symm)
      (pullback.fst (V.f i ≫ t) (V.f j ≫ t) ≫ V.f i ≫ t)
      (pullback.fst (U.f i ≫ s) (U.f j ≫ s) ≫ (U.f i ≫ s)) κ := by
  dsimp only [Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  simpa only [Category.comp_id] using
    overlap_square (U.f i ≫ s) (U.f j ≫ s) (𝟙 B) κ
      _ _ (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) κ
      _ _ (𝟙 T) (by simpa using chart_square κ s (U.f i))
      (by simpa using chart_square κ s (U.f j)) (IsPullback.of_id_snd (f := κ))
      (chart_square κ s (U.f i)).w.symm
      (chart_square κ s (U.f j)).w.symm (by simp) (by simp)

/-- Scalar extension of the overlap graph, with its coefficient projection
as the first pullback projection. -/
def scalarCoverGraph {B T X : Scheme.{u}} (κ : T ⟶ B) (s : X ⟶ B)
    (U : X.OpenCover.{u}) (i j : U.I₀) :
    pullback κ (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) ⟶
      pullback κ (pullback.fst (U.f i ≫ s) (U.f j ≫ s) ≫ (U.f i ≫ s)) :=
  pullback.map κ _ κ _ (𝟙 T) (coverOverlapGraph U s i j) (𝟙 B)
    (by simp) (by simp [coverOverlapGraph])

private theorem graph_fst_after {X S Z : Scheme.{u}} (U : X.OpenCover.{u})
    (s : X ⟶ S) (i j : U.I₀) (h : U.X i ⟶ Z) :
    coverOverlapGraph U s i j ≫ pullback.fst (U.f i ≫ s) (U.f j ≫ s) ≫ h =
      pullback.fst (U.f i) (U.f j) ≫ h := by
  rw [← Category.assoc, coverOverlapGraph_fst]

private theorem graph_snd_after {X S Z : Scheme.{u}} (U : X.OpenCover.{u})
    (s : X ⟶ S) (i j : U.I₀) (h : U.X j ⟶ Z) :
    coverOverlapGraph U s i j ≫ pullback.snd (U.f i ≫ s) (U.f j ≫ s) ≫ h =
      pullback.snd (U.f i) (U.f j) ≫ h := by
  rw [← Category.assoc, coverOverlapGraph_snd]

/-- The overlap graph of a scalar cover agrees with the scalar overlap graph. -/
theorem graph_comparison {B T X : Scheme.{u}}
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u}) (i j : U.I₀) :
    let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
    coverOverlapGraph V (pullback.fst κ s) i j ≫
        (scalar_product_square κ s U i j).flip.isoPullback.hom =
      (scalarCoverOverlapIso κ s U i j).hom ≫ scalarCoverGraph κ s U i j := by
  let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
  let E := scalarCoverOverlapIso κ s U i j
  let P := (scalar_product_square κ s U i j).flip.isoPullback
  have hEt : E.hom ≫ pullback.fst _ _ =
      pullback.fst (V.f i) (V.f j) ≫ V.f i ≫ pullback.fst κ s :=
    (scalar_overlap_square κ s U i j).flip.isoPullback_hom_fst
  have hEq : E.hom ≫ pullback.snd _ _ =
      pullback.map (V.f i) (V.f j) (U.f i) (U.f j)
        (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) (pullback.snd κ s)
        pullback.condition pullback.condition :=
    (scalar_overlap_square κ s U i j).flip.isoPullback_hom_snd
  have hPt : P.hom ≫ pullback.fst _ _ =
      pullback.fst (V.f i ≫ pullback.fst κ s) (V.f j ≫ pullback.fst κ s) ≫
        V.f i ≫ pullback.fst κ s :=
    (scalar_product_square κ s U i j).flip.isoPullback_hom_fst
  have hPq : P.hom ≫ pullback.snd _ _ =
      pullback.map (V.f i ≫ pullback.fst κ s) (V.f j ≫ pullback.fst κ s)
        (U.f i ≫ s) (U.f j ≫ s)
        (pullback.snd _ (U.f i)) (pullback.snd _ (U.f j)) κ
        (chart_square κ s (U.f i)).w.symm
        (chart_square κ s (U.f j)).w.symm :=
    (scalar_product_square κ s U i j).flip.isoPullback_hom_snd
  change coverOverlapGraph V (pullback.fst κ s) i j ≫ P.hom =
    E.hom ≫ scalarCoverGraph κ s U i j
  apply pullback.hom_ext
  · simp only [Category.assoc, hPt, scalarCoverGraph, pullback.map,
      pullback.lift_fst, Category.comp_id, hEt]
    exact graph_fst_after V (pullback.fst κ s) i j (V.f i ≫ pullback.fst κ s)
  · apply pullback.hom_ext
    · simp only [Category.assoc, hPq, scalarCoverGraph, pullback.map,
        pullback.lift_fst, pullback.lift_snd, Category.comp_id]
      have he : E.hom ≫ pullback.snd _ _ ≫ pullback.fst (U.f i) (U.f j) =
          pullback.fst (V.f i) (V.f j) ≫ pullback.snd _ (U.f i) := by
        simpa only [Category.assoc, pullback.map, pullback.lift_fst] using
          congrArg (fun z => z ≫ pullback.fst (U.f i) (U.f j)) hEq
      have hg := congrArg
        (fun z => E.hom ≫ pullback.snd κ
          (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) ≫ z)
        (coverOverlapGraph_fst U s i j)
      exact (graph_fst_after V (pullback.fst κ s) i j
        (pullback.snd _ (U.f i))).trans (he.symm.trans
          (by simpa only [Category.assoc] using hg.symm))
    · simp only [Category.assoc, hPq, scalarCoverGraph, pullback.map,
        pullback.lift_snd, Category.comp_id]
      have he : E.hom ≫ pullback.snd _ _ ≫ pullback.snd (U.f i) (U.f j) =
          pullback.snd (V.f i) (V.f j) ≫ pullback.snd _ (U.f j) := by
        simpa only [Category.assoc, pullback.map, pullback.lift_snd] using
          congrArg (fun z => z ≫ pullback.snd (U.f i) (U.f j)) hEq
      have hg := congrArg
        (fun z => E.hom ≫ pullback.snd κ
          (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) ≫ z)
        (coverOverlapGraph_snd U s i j)
      exact (graph_snd_after V (pullback.fst κ s) i j
        (pullback.snd _ (U.f j))).trans (he.symm.trans
          (by simpa only [Category.assoc] using hg.symm))

/-- Closed scalar overlap graphs of an open cover make the scalar structure
morphism separated. -/
theorem separated_scalar_of_graphs {B T X : Scheme.{u}}
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u})
    (h : ∀ i j, IsClosedImmersion (scalarCoverGraph κ s U i j)) :
    IsSeparated (pullback.fst κ s) := by
  let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
  apply separated_of_cover_graphs V (pullback.fst κ s)
  intro i j
  let E := scalarCoverOverlapIso κ s U i j
  let P := (scalar_product_square κ s U i j).flip.isoPullback
  let : IsClosedImmersion (scalarCoverGraph κ s U i j) := h i j
  have he : coverOverlapGraph V (pullback.fst κ s) i j =
      E.hom ≫ scalarCoverGraph κ s U i j ≫ P.inv := by
    calc
      _ = (coverOverlapGraph V (pullback.fst κ s) i j ≫ P.hom) ≫ P.inv := by simp
      _ = _ := by
        have hg : coverOverlapGraph V (pullback.fst κ s) i j ≫ P.hom =
            E.hom ≫ scalarCoverGraph κ s U i j := graph_comparison κ s U i j
        exact (congrArg (fun z => z ≫ P.inv) hg).trans (Category.assoc _ _ _)
  rw [he]
  infer_instance



end
end FrobeniusSplitting
