import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateCocone
import OrbitComplexity.FrobeniusSplitting.Normality.GluedComparisons
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels

/-! # Scalar extension of a fixed affine gluing cocone

Tensoring the affine diagram extends its chosen glued scheme by the same
coefficient map. The comparison targets the prescribed cocone, and its
restriction to every chart is the tensor inclusion followed by the old leg.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

open private specScalarTransformation from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateCocone

namespace FrobeniusSplitting

universe u v w

private theorem tensor_inclusion_cart {S R A : Type u}
    [CommRing S] [CommRing R] [CommRing A] [Algebra S R] [Algebra S A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[S] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap S A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) := by
  have he : tensorImageHom (AlgEquiv.refl : R ⊗[S] A ≃ₐ[R] R ⊗[S] A) =
      Algebra.TensorProduct.includeRight := by
    ext a
    rfl
  simpa only [he] using
    (isPullback_affineModel (AlgEquiv.refl : R ⊗[S] A ≃ₐ[R] R ⊗[S] A)).flip

/-- The chartwise tensor inclusions form a natural map of coefficient diagrams. -/
def fixedScalarMap {J : Type v} [Category.{w} J]
    (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]
    (N : J ⥤ CommAlgCat.{u} S) :
    N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      fixedFibreDiagram (R := R) (M := R) N ⋙ forget₂ (CommAlgCat R) CommRingCat where
  app i := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : N.obj i →ₐ[S] R ⊗[S] N.obj i).toRingHom
  naturality {i j} f := by
    apply CommRingCat.hom_ext
    ext a
    rfl

private theorem equifibered_of_cart {J : Type v} [Category.{w} J]
    {B D : Scheme.{u}} (F : J ⥤ Over B) (G : J ⥤ Over D) (κ : B ⟶ D)
    (α : F ⋙ Over.forget B ⟶ G ⋙ Over.forget D)
    (hcart : ∀ i, IsPullback (α.app i) (F.obj i).hom (G.obj i).hom κ) :
    α.Equifibered := by
  intro i j f
  have hs : IsPullback ((F.map f).left ≫ (F.obj j).hom) (α.app i) κ
      ((G.map f).left ≫ (G.obj j).hom) := by
    simpa only [Over.w] using (hcart i).flip
  exact hs.of_right (α.naturality f) (hcart j).flip

private theorem exists_fixed_comparison {J : Type v} [Category.{w} J]
    [Quiver.IsThin J] [Small.{u} J] {B D : Scheme.{u}}
    (F : J ⥤ Over B) (G : J ⥤ Over D) (κ : B ⟶ D)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion ((G.map f).left)]
    [((G ⋙ Over.forget D) ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⋙ Over.forget B ⟶ G ⋙ Over.forget D) (hα : α.Equifibered)
    (hcart : ∀ i, IsPullback (α.app i) (F.obj i).hom (G.obj i).hom κ)
    (cG : Cocone G) (hcG : IsColimit cG) :
    ∃ (cF : Cocone F) (q : cF.pt.left ⟶ cG.pt.left),
      Nonempty (IsColimit cF) ∧ IsPullback q cF.pt.hom cG.pt.hom κ ∧
        ∀ i, (cF.ι.app i).left ≫ q = α.app i ≫ (cG.ι.app i).left := by
  obtain ⟨cF, cO, q, hcF, ⟨hcO⟩, hq, hleg⟩ :=
    exists_glued_comparisons F G κ α hα hcart
  let E : cO.pt ≅ cG.pt := hcO.coconePointUniqueUpToIso hcG
  have hE : IsPullback E.hom.left cO.pt.hom cG.pt.hom (𝟙 D) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using E.hom.w⟩
  refine ⟨cF, q ≫ E.hom.left, hcF, ?_, ?_⟩
  · simpa only [Category.comp_id] using hq.paste_horiz hE
  · intro i
    have hi : (cO.ι.app i).left ≫ E.hom.left = (cG.ι.app i).left :=
      congrArg Over.Hom.left (hcO.comp_coconePointUniqueUpToIso_hom hcG i)
    rw [← Category.assoc, hleg, Category.assoc, hi]

/-- Tensor extension of an affine diagram gives a Cartesian cocone comparison
to its prescribed colimit, preserving every original chart leg. -/
theorem exists_fixed_scalar_cocone {J : Type v} [Category.{w} J]
    [Quiver.IsThin J] [Small.{u} J]
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    (N : J ⥤ CommAlgCat.{u} S)
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j),
      IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left)]
    [(((N.op ⋙ algSpec (.of S)) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of S))) (hcG : IsColimit cG) :
    let NR := fixedFibreDiagram (R := R) (M := R) N
    (∀ {i j : Jᵒᵖ} (f : i ⟶ j),
      IsOpenImmersion (((NR.op ⋙ algSpec (.of R)).map f).left)) ∧
      ((((NR.op ⋙ algSpec (.of R)) ⋙ Over.forget (Spec (.of R))) ⋙
        Scheme.forget).IsLocallyDirected) ∧
      ∃ (cR : Cocone (NR.op ⋙ algSpec (.of R))) (q : cR.pt.left ⟶ cG.pt.left),
        Nonempty (IsColimit cR) ∧
          IsPullback q cR.pt.hom cG.pt.hom
            (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
          ∀ i, (cR.ι.app i).left ≫ q =
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight :
                N.obj i.unop →ₐ[S] R ⊗[S] N.obj i.unop).toRingHom) ≫
                (cG.ι.app i).left := by
  let NR := fixedFibreDiagram (R := R) (M := R) N
  let F := NR.op ⋙ algSpec (.of R)
  let G := N.op ⋙ algSpec (.of S)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let α : F ⋙ Over.forget (Spec (.of R)) ⟶
      G ⋙ Over.forget (Spec (.of S)) :=
    specScalarTransformation _ _ (fixedScalarMap S R N)
  have hcart (i : Jᵒᵖ) : IsPullback (α.app i) (F.obj i).hom (G.obj i).hom κ :=
    tensor_inclusion_cart
  have hα : α.Equifibered := equifibered_of_cart F G κ α hcart
  have hopen {i j : Jᵒᵖ} (f : i ⟶ j) : IsOpenImmersion ((F.map f).left) :=
    MorphismProperty.of_isPullback (hα f).flip
      (inferInstanceAs (IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left)))
  let : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsOpenImmersion ((F.map f).left) := hopen
  have hdir : ((F ⋙ Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective α hα
      (fun f ↦ ((F.map f).left).isOpenEmbedding.injective)
  refine ⟨hopen, hdir, ?_⟩
  exact exists_fixed_comparison F G κ α hα hcart cG hcG

end FrobeniusSplitting
