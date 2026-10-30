import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.GluedComparisons
import OrbitComplexity.FrobeniusSplitting.Normality.AffineModelDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.GluedFiniteness

/-!
# Colimits of affine model diagrams
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A locally directed affine model diagram glues with its scalar comparison and finiteness. -/
theorem exists_affine_model_colimit {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    [Finite C] {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (D₀ : C ⥤ CommAlgCat.{u} R) (D : C ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i)
    [∀ i, Algebra.FinitePresentation R (D₀.obj i)]
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D₀.map f).hom.toRingHom))]
    [((D₀.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected] :
    ∃ (cF : Cocone (D.op ⋙ algSpec (.of K)))
      (cG : Cocone (D₀.op ⋙ algSpec (.of R))) (q : cF.pt.left ⟶ cG.pt.left),
      Nonempty (IsColimit cF) ∧ Nonempty (IsColimit cG) ∧
      IsPullback q cF.pt.hom cG.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      (∀ i, (cF.ι.app i).left ≫ q =
        (affineModelNatTrans D₀ D e hnatural).app i ≫ (cG.ι.app i).left) ∧
      CompactSpace cG.pt.left ∧ LocallyOfFinitePresentation cG.pt.hom := by
  let F := D.op ⋙ algSpec (.of K)
  let G := D₀.op ⋙ algSpec (.of R)
  have : ((G ⋙ Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected :=
    inferInstanceAs (((D₀.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected)
  have {i j : Cᵒᵖ} (f : i ⟶ j) : IsOpenImmersion (G.map f).left :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D₀.map f.unop).hom.toRingHom)))
  obtain ⟨cF, cG, q, hF, hG, hcart, hcomp⟩ := exists_glued_comparisons F G
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (affineModelNatTrans D₀ D e hnatural) (affineModel_equifibered D₀ D e hnatural)
    (fun i ↦ by
      let : Algebra R (D.obj i.unop) :=
        ((algebraMap K (D.obj i.unop)).comp (algebraMap R K)).toAlgebra
      have htower : IsScalarTower R K (D.obj i.unop) :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      exact (@isPullback_affineModel R K (D₀.obj i.unop) (D.obj i.unop)
        _ _ _ _ _ _ _ _ htower (e i.unop)).flip)
  have (i : Cᵒᵖ) : IsAffine (G.obj i).left :=
    inferInstanceAs (IsAffine (Spec (.of (D₀.obj i.unop))))
  have (i : Cᵒᵖ) : LocallyOfFinitePresentation (G.obj i).hom := by
    change LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (D₀.obj i.unop))))
    apply (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R (D₀.obj i.unop)))).mpr
    change (algebraMap R (D₀.obj i.unop)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have : Finite Cᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨hcompact, hfp⟩ := finite_affine_colimit_properties G cG hG.some
  exact ⟨cF, cG, q, hF, hG, hcart, hcomp, hcompact, hfp⟩

end FrobeniusSplitting
