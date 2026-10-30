import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.TensorSchemeIso
import OrbitComplexity.FrobeniusSplitting.Normality.AffineModelColimits

/-!
# ModelTensorSquares

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

set_option maxHeartbeats 400000 in
/-- A finite coefficient model with common-base fixed-fibre coordinates glues to
a product square, with its base and fibre chart equations retained. -/
theorem exists_model_tensor_square {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    [Finite J] {S R M : Type u} [CommRing S] [CommRing R] [CommRing M]
    [Algebra S R] [Algebra R M] [Algebra S M] [IsScalarTower S R M]
    (G : J ⥤ CommAlgCat.{u} S) (D : J ⥤ CommAlgCat.{u} R)
    [∀ i, Algebra.FinitePresentation S (G.obj i)]
    (iso : D ≅ fixedFibreDiagram (R := R) (M := M) G)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (G.map f).hom.toRingHom))]
    [((G.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cD : Cocone (D.op ⋙ algSpec (.of R)))
    (cG : Cocone (G.op ⋙ algSpec (.of S)))
    (hcD : IsColimit cD) (hcG : IsColimit cG) :
    ∃ (base : cD.pt.left ⟶ Spec (.of M)) (q : cD.pt.left ⟶ cG.pt.left),
      IsPullback q base cG.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap S M))) ∧
      (∀ i, (cD.ι.app i).left ≫ base =
        Spec.map (CommRingCat.ofHom
          ((iso.inv.app i.unop).hom.toRingHom.comp
            (Algebra.TensorProduct.includeLeft :
              M →ₐ[M] M ⊗[S] G.obj i.unop).toRingHom))) ∧
      ∀ i, (cD.ι.app i).left ≫ q =
        Spec.map (CommRingCat.ofHom
          ((iso.inv.app i.unop).hom.toRingHom.comp
            Algebra.TensorProduct.includeRight.toRingHom)) ≫ (cG.ι.app i).left := by
  let T := fixedFibreDiagram (R := M) (M := M) G
  let cmp (i : J) : M ⊗[S] G.obj i ≃ₐ[M] T.obj i := AlgEquiv.refl
  have hnatural : ∀ i j (f : i ⟶ j), (cmp j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := M) M (G.map f).hom) =
        (T.map f).hom.comp (cmp i).toAlgHom := by
    intro i j f
    rfl
  obtain ⟨cT, cG', q', ⟨hcT⟩, ⟨hcG'⟩, hcart, hcomp, _, _⟩ :=
    exists_affine_model_colimit G T cmp hnatural
  let es := tensorSchemeIso G D iso
  let c := (Cocone.precompose es.hom).obj
    ((Over.forget (Spec (.of M))).mapCocone cT)
  have hc : IsColimit c :=
    (IsColimit.precomposeHomEquiv es _).symm
      (isColimitOfPreserves (Over.forget (Spec (.of M))) hcT)
  let hD := isColimitOfPreserves (Over.forget (Spec (.of R))) hcD
  let eX := hD.coconePointUniqueUpToIso hc
  let eZ := (Over.forget (Spec (.of S))).mapIso
    (hcG'.coconePointUniqueUpToIso hcG)
  have hX (i : Jᵒᵖ) :
      (cD.ι.app i).left ≫ eX.hom = es.hom.app i ≫ (cT.ι.app i).left :=
    hD.comp_coconePointUniqueUpToIso_hom hc i
  have hZ (i : Jᵒᵖ) : (cG'.ι.app i).left ≫ eZ.hom = (cG.ι.app i).left :=
    congrArg (fun f ↦ f.left) (hcG'.comp_coconePointUniqueUpToIso_hom hcG i)
  let base := eX.hom ≫ cT.pt.hom
  let q := eX.hom ≫ q' ≫ eZ.hom
  refine ⟨base, q, ?_, ?_, ?_⟩
  · apply hcart.of_iso' eX eZ.symm (Iso.refl _) (Iso.refl _)
    · simp [q, Category.assoc]
    · simp [base]
    · change eZ.inv ≫ cG'.pt.hom = cG.pt.hom ≫ 𝟙 _
      rw [Category.comp_id]
      exact Over.w (hcG'.coconePointUniqueUpToIso hcG).inv
    · simp
  · intro i
    change (cD.ι.app i).left ≫ (eX.hom ≫ cT.pt.hom) = _
    calc
      _ = ((cD.ι.app i).left ≫ eX.hom) ≫ cT.pt.hom := (Category.assoc _ _ _).symm
      _ = (es.hom.app i ≫ (cT.ι.app i).left) ≫ cT.pt.hom :=
        congrArg (fun z ↦ z ≫ cT.pt.hom) (hX i)
      _ = es.hom.app i ≫ ((cT.ι.app i).left ≫ cT.pt.hom) := Category.assoc _ _ _
      _ = es.hom.app i ≫ Spec.map
          (CommRingCat.ofHom (algebraMap M (T.obj i.unop))) :=
        congrArg (fun z ↦ es.hom.app i ≫ z) (Over.w (cT.ι.app i))
      _ = _ := by
        change Spec.map (CommRingCat.ofHom (iso.inv.app i.unop).hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap M (T.obj i.unop))) = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl
  · intro i
    change (cD.ι.app i).left ≫ (eX.hom ≫ q' ≫ eZ.hom) = _
    calc
      _ = (es.hom.app i ≫ (cT.ι.app i).left) ≫ (q' ≫ eZ.hom) := by
        rw [← Category.assoc, hX]
      _ = es.hom.app i ≫
          ((affineModelNatTrans G T cmp hnatural).app i ≫ (cG'.ι.app i).left) ≫
            eZ.hom := by
        rw [Category.assoc, ← Category.assoc (cT.ι.app i).left, hcomp]
      _ = (es.hom.app i ≫ (affineModelNatTrans G T cmp hnatural).app i) ≫
          (cG.ι.app i).left := by
        simp only [Category.assoc, hZ]
      _ = _ := by
        congr 1
        change Spec.map (CommRingCat.ofHom (iso.inv.app i.unop).hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end FrobeniusSplitting
