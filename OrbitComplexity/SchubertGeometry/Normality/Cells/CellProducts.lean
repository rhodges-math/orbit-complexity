import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedScalarComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
import OrbitComplexity.SchubertGeometry.BSDH.CellFibres
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # cell products on the specified endpoint and flag models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting CartesianMonoidalCategory
open scoped MonoidalCategory

namespace SchubertGeometry

universe u

private abbrev wordEndpoint
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (bsdhMap G word) rfl

private theorem rawPB_base {K : Scheme.{u}} {X Y F : Over K}
    (f : X ⟶ F) (g : Y ⟶ F) :
    pullback.fst f.left g.left ≫ X.hom = pullback.snd f.left g.left ≫ Y.hom := by
  calc
    _ = (pullback.fst f.left g.left ≫ f.left) ≫ F.hom :=
      (congrArg (fun z => pullback.fst f.left g.left ≫ z) f.w.symm).trans
        (Category.assoc _ _ _).symm
    _ = (pullback.snd f.left g.left ≫ g.left) ≫ F.hom :=
      congrArg (fun z => z ≫ F.hom) (pullback.condition (f := f.left) (g := g.left))
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun z => pullback.snd f.left g.left ≫ z) g.w)

private theorem inverse_projection {D : Type*} [Category D]
    {A B C : D} (e : A ≅ B) (q : A ⟶ C) (p : B ⟶ C)
    (h : e.hom ≫ p = q) : e.inv ≫ q = p := by
  exact (congrArg (fun z => e.inv ≫ z) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ p) e.inv_hom_id).trans (Category.id_comp _)))

private theorem overPB_scalar
    {K S : Scheme.{u}} (κ : K ⟶ S)
    (X Y F : Over K) (X₀ Y₀ F₀ : Over S)
    (f : X ⟶ F) (g : Y ⟶ F) (f₀ : X₀ ⟶ F₀) (g₀ : Y₀ ⟶ F₀)
    (qX : X.left ⟶ X₀.left) (qY : Y.left ⟶ Y₀.left) (qF : F.left ⟶ F₀.left)
    (hX : IsPullback qX X.hom X₀.hom κ)
    (hY : IsPullback qY Y.hom Y₀.hom κ)
    (hF : IsPullback qF F.hom F₀.hom κ)
    (hf : f.left ≫ qF = qX ≫ f₀.left)
    (hg : g.left ≫ qF = qY ≫ g₀.left) :
    ∃ q : (pullback f g).left ⟶ pullback f₀.left g₀.left,
      IsPullback q (pullback f g).hom
        (pullback.snd f₀.left g₀.left ≫ Y₀.hom) κ ∧
      q ≫ pullback.snd f₀.left g₀.left = (pullback.snd f g).left ≫ qY := by
  let e : (pullback f g).left ≅ pullback f.left g.left :=
    PreservesPullback.iso (Over.forget K) f g
  let qr := pullback.map f.left g.left f₀.left g₀.left qX qY qF hf hg
  obtain ⟨hr, _, hrs⟩ := paired_model_scalar_pullback κ X.hom Y.hom F.hom
    X₀.hom Y₀.hom F₀.hom f.left g.left f₀.left g₀.left
    f.w g.w f₀.w g₀.w qX qY qF hX hY hF hf hg
  rw [rawPB_base f g, rawPB_base f₀ g₀] at hr
  have hes : e.hom ≫ pullback.snd f.left g.left = (pullback.snd f g).left :=
    PreservesPullback.iso_hom_snd (Over.forget K) f g
  have hbase : e.hom ≫ (pullback.snd f.left g.left ≫ Y.hom) =
      (pullback f g).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ Y.hom) hes).trans (pullback.snd f g).w)
  have hi : IsPullback e.hom (pullback f g).hom
      (pullback.snd f.left g.left ≫ Y.hom) (𝟙 K) :=
    IsPullback.of_horiz_isIso ⟨hbase.trans (Category.comp_id _).symm⟩
  refine ⟨e.hom ≫ qr, ?_, ?_⟩
  · simpa only [Category.id_comp] using hi.paste_horiz hr
  · calc
      (e.hom ≫ qr) ≫ pullback.snd f₀.left g₀.left =
          e.hom ≫ (pullback.snd f.left g.left ≫ qY) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => e.hom ≫ z) hrs)
      _ = (pullback.snd f g).left ≫ qY :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ qY) hes)

/-- The BSDH cell trivialization gives an isomorphism of the
generic fibres of the prescribed pullback models. Its map preserves the
original cell projection; no arithmetic group or action is assumed. -/
theorem bsdhCell_model_product
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (w : G.weylGroup)
    (Z F C : Over (Spec (.of S))) (f : Z ⟶ F) (c : C ⟶ F)
    (b : Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qZ : (bsdhVariety G word).scheme ⟶ Z.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qC : (schubertCell G w).scheme ⟶ C.left)
    (hZ : IsPullback qZ (bsdhVariety G word).toSpec Z.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : IsPullback qC (schubertCell G w).toSpec C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : (wordEndpoint G word).left ≫ qF = qZ ≫ f.left)
    (hc : (schubertCellInclusion G w).left ≫ qF = qC ≫ c.left)
    (hb : (weylFlagPoint G w).val ≫ qF =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ b.left) :
    let a := pullback.snd f.left c.left ≫ C.hom
    let W := Over.mk (pullback.snd f.left b.left)
    let P := C ⊗ W
    ∃ E : genericScalarModel S a ≅ genericScalarModel S P.hom,
      E.hom.left ≫ pullback.snd _ P.hom ≫ pullback.fst C.hom W.hom =
        pullback.snd _ a ≫ pullback.snd f.left c.left := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let CK := (schubertCell G w).toOver
  let fK := wordEndpoint G word
  let cK := schubertCellInclusion G w
  let yK := (flagVariety G).pointsEquivOverHom (weylFlagPoint G w)
  let AK := pullback fK cK
  let WK := pullback fK yK
  let PK := CK ⊗ WK
  let a := pullback.snd f.left c.left ≫ C.hom
  let W : Over (Spec (.of S)) := Over.mk (pullback.snd f.left b.left)
  let P := C ⊗ W
  obtain ⟨qA, hA, hAc⟩ := overPB_scalar κ
    (bsdhVariety G word).toOver CK (flagVariety G).toOver Z C F fK cK f c
    qZ qC qF hZ hC hF hf hc
  have hpoint : IsPullback κ (𝟙 (Spec (.of K))) (𝟙 (Spec (.of S))) κ :=
    IsPullback.of_id_snd
  obtain ⟨qW, hW, _⟩ := overPB_scalar κ
    (bsdhVariety G word).toOver (𝟙_ (Over (Spec (.of K))))
    (flagVariety G).toOver Z (Over.mk (𝟙 (Spec (.of S)))) F fK yK f b
    qZ κ qF hZ hpoint hF hf hb
  let qP : PK.left ⟶ P.left :=
    pullback.map CK.hom WK.hom C.hom W.hom qC qW κ hC.w.symm hW.w.symm
  obtain ⟨hP, hPC, _⟩ := paired_model_scalar_pullback κ CK.hom WK.hom
    (𝟙 (Spec (.of K))) C.hom W.hom (𝟙 (Spec (.of S)))
    CK.hom WK.hom C.hom W.hom (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _) (Category.comp_id _) qC qW κ hC hW hpoint hC.w.symm hW.w.symm
  let eA : AK ≅ genericScalarModel S a :=
    Over.isoMk hA.flip.isoPullback hA.flip.isoPullback_hom_fst
  let eP : PK ≅ genericScalarModel S P.hom :=
    Over.isoMk hP.flip.isoPullback hP.flip.isoPullback_hom_fst
  obtain ⟨e, he, _, _, _⟩ := bsdhCellTrivialization G word w
  let E : genericScalarModel S a ≅ genericScalarModel S P.hom := eA.symm ≪≫ e ≪≫ eP
  have heA : eA.hom.left ≫ pullback.snd κ a = qA := hA.flip.isoPullback_hom_snd
  have heP : eP.hom.left ≫ pullback.snd κ P.hom = qP := hP.flip.isoPullback_hom_snd
  have hec : e.hom.left ≫ (fst CK WK).left = (pullback.snd fK cK).left :=
    congrArg Over.Hom.left he
  let EA : AK.left ≅ pullback κ a := (Over.forget (Spec (.of K))).mapIso eA
  let EP : PK.left ≅ pullback κ P.hom := (Over.forget (Spec (.of K))).mapIso eP
  let α : (pullback κ a : Scheme.{u}) ⟶ AK.left := EA.inv
  let ε : AK.left ⟶ PK.left := e.hom.left
  let γ : PK.left ⟶ pullback κ P.hom := EP.hom
  let sA : (pullback κ a : Scheme.{u}) ⟶ pullback f.left c.left := pullback.snd κ a
  let sP : (pullback κ P.hom : Scheme.{u}) ⟶ P.left := pullback.snd κ P.hom
  let d : (pullback f.left c.left : Scheme.{u}) ⟶ C.left := pullback.snd f.left c.left
  let pC : P.left ⟶ C.left := pullback.fst C.hom W.hom
  let cA : AK.left ⟶ CK.left := (pullback.snd fK cK).left
  let cP : PK.left ⟶ CK.left := (fst CK WK).left
  have hγ : γ ≫ sP = qP := heP
  have hε : ε ≫ cP = cA := hec
  have hqP : qP ≫ pC = cP ≫ qC := hPC
  have hqA : qA ≫ d = cA ≫ qC := hAc
  have hα : α ≫ qA = sA := inverse_projection EA qA sA heA
  refine ⟨E, ?_⟩
  change ((α ≫ ε) ≫ γ) ≫ sP ≫ pC = sA ≫ d
  calc
    _ = (α ≫ ε) ≫ (qP ≫ pC) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => (α ≫ ε) ≫ z)
          (((Category.assoc _ _ _).symm).trans (congrArg (fun z => z ≫ pC) hγ)))
    _ = (α ≫ ε) ≫ (cP ≫ qC) := congrArg (fun z => (α ≫ ε) ≫ z) hqP
    _ = α ≫ (cA ≫ qC) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => α ≫ z)
          (((Category.assoc _ _ _).symm).trans (congrArg (fun z => z ≫ qC) hε)))
    _ = α ≫ (qA ≫ d) := congrArg (fun z => α ≫ z) hqA.symm
    _ = sA ≫ d :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ d) hα)


end SchubertGeometry
