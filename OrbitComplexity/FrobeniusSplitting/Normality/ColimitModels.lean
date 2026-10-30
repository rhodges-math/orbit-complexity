import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.AffineModelColimits

/-!
# Affine models of specified generic colimits
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- An affine model diagram gives a model of any specified colimit of its generic diagram. -/
theorem exists_affine_model_for_colimit
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] [Finite C]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (D₀ : C ⥤ CommAlgCat.{u} R) (D : C ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i)
    [∀ i, Algebra.FinitePresentation R (D₀.obj i)]
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D₀.map f).hom.toRingHom))]
    [((D₀.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cX : Cocone (D.op ⋙ algSpec (.of K))) (hcX : IsColimit cX) :
    ∃ (cG : Cocone (D₀.op ⋙ algSpec (.of R))) (q : cX.pt.left ⟶ cG.pt.left),
      Nonempty (IsColimit cG) ∧
      IsPullback q cX.pt.hom cG.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      (∀ i, (cX.ι.app i).left ≫ q =
        (affineModelNatTrans D₀ D e hnatural).app i ≫ (cG.ι.app i).left) ∧
      CompactSpace cG.pt.left ∧ LocallyOfFinitePresentation cG.pt.hom := by
  obtain ⟨cF, cG, q, ⟨hcF⟩, hG, hcart, hcomp, hcompact, hfp⟩ :=
    exists_affine_model_colimit D₀ D e hnatural
  let isoX := hcX.coconePointUniqueUpToIso hcF
  let isoS := (Over.forget (Spec (.of K))).mapIso isoX
  have hcartX : IsPullback (isoS.hom ≫ q) cX.pt.hom cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    apply hcart.of_iso' isoS (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · change isoX.hom.left ≫ cF.pt.hom = cX.pt.hom ≫ 𝟙 _
      rw [Category.comp_id]
      exact Over.w isoX.hom
    · simp
    · simp
  refine ⟨cG, isoS.hom ≫ q, hG, hcartX, ?_, hcompact, hfp⟩
  intro i
  have hι : (cX.ι.app i).left ≫ isoS.hom = (cF.ι.app i).left :=
    congrArg (fun t ↦ t.left) (hcX.comp_coconePointUniqueUpToIso_hom hcF i)
  rw [← Category.assoc, hι, hcomp]

end FrobeniusSplitting
