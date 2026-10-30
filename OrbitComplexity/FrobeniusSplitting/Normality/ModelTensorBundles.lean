import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ModelTensorSquares
import OrbitComplexity.FrobeniusSplitting.Normality.TensorBaseComp
import OrbitComplexity.FrobeniusSplitting.Normality.BundleProperties

/-!
# ModelTensorBundles

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A retained fixed-fibre diagram gives a coefficient-model projection with the
properness, smoothness and connected geometric fibres of the specified fibre. -/
theorem exists_model_tensor_bundle {J : Type u} [Category.{u} J] [Quiver.IsThin J]
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
    [IsProper cG.pt.hom] [Smooth cG.pt.hom] [GeometricallyConnected cG.pt.hom]
    (hcD : IsColimit cD) (hcG : IsColimit cG) :
    ∃ (base : cD.pt.left ⟶ Spec (.of M)) (q : cD.pt.left ⟶ cG.pt.left),
      (base ≫ Spec.map (CommRingCat.ofHom (algebraMap R M)) = cD.pt.hom) ∧
      IsProper base ∧ Smooth base ∧ GeometricallyConnected base ∧
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
  obtain ⟨base, q, hcart, hbase, hq⟩ :=
    exists_model_tensor_square G D iso cD cG hcD hcG
  have hcoeff := tensor_base_comp G D iso cD hcD base hbase
  have hproper : IsProper base := MorphismProperty.of_isPullback hcart inferInstance
  have hsmooth : Smooth base := MorphismProperty.of_isPullback hcart inferInstance
  have hconn : geometrically (ConnectedSpace ·) base :=
    MorphismProperty.of_isPullback hcart
      (GeometricallyConnected.geometrically_connectedSpace (f := cG.pt.hom))
  exact ⟨base, q, hcoeff, hproper, hsmooth, ⟨hconn⟩, hcart, hbase, hq⟩

end FrobeniusSplitting
