import OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Closed target objects from coordinate atlases

The coordinate cocones give closed target models with Cartesian
comparisons. Their scheme objects, inclusions and finiteness properties
are retained before specializing the ambient scheme.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

noncomputable section
universe u v

namespace SchubertGeometry

open private target_result
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing

private def closed_target_stage {K : Type u} [CommRing K] {I : Type v}
    (S : Subalgebra ℤ K) (Y : Over (Spec (.of K)))
    (X : I → Over (Spec (.of K))) (j : ∀ i, X i ⟶ Y)
    (P : Over (Spec (.of S))) (qP : Y.left ⟶ P.left)
    (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k)
    (D : I → Over (Spec (.of k.val)))
    (iD : ∀ i, D i ⟶ stageScalarModel S P.hom k)
    (qPk : Y.left ⟶ (stageScalarModel S P.hom k).left)
    (qD : ∀ i, (X i).left ⟶ (D i).left),
    IsPullback qPk Y.hom (stageScalarModel S P.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    qPk ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
      P.hom = qP ∧
    ∀ i, IsClosedImmersion (iD i).left ∧
      IsPullback (qD i) (X i).hom (D i).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
      qD i ≫ (iD i).left = (j i).left ≫ qPk ∧
      LocallyOfFinitePresentation (D i).hom ∧
      CompactSpace (D i).left ∧ QuasiSeparatedSpace (D i).left

private theorem target_objects
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {C : Type u} [Category.{u} C] {I : Type v}
    (F₀ : C ⥤ CommAlgCat.{u} S) (B₀ : I → C ⥤ CommAlgCat.{u} S)
    (β₀ : ∀ i, F₀ ⟶ B₀ i)
    (F : C ⥤ CommAlgCat.{u} K) (B : I → C ⥤ CommAlgCat.{u} K)
    (eF : ∀ c, K ⊗[S] F₀.obj c ≃ₐ[K] F.obj c)
    (eB : ∀ i c, K ⊗[S] (B₀ i).obj c ≃ₐ[K] (B i).obj c)
    (hF : ∀ c d (f : c ⟶ d), (eF d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map f).hom) =
      (F.map f).hom.comp (eF c).toAlgHom)
    (hB : ∀ i c d (f : c ⟶ d), (eB i d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map f).hom) =
      ((B i).map f).hom.comp (eB i c).toAlgHom)
    (cFN : Cocone (F.op ⋙ algSpec (.of K)))
    (cBN : ∀ i, Cocone ((B i).op ⋙ algSpec (.of K)))
    (jN : ∀ i, (cBN i).pt ⟶ cFN.pt)
    (P : Over (Spec (.of S))) (qP : cFN.pt.left ⟶ P.left)
    (hP : IsPullback qP cFN.pt.hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S)
    (hdata : target_result S F₀ B₀ β₀ F B eF eB hF hB cFN cBN jN P qP hP start) :
    closed_target_stage S cFN.pt (fun i => (cBN i).pt) jN P qP start := by
  classical
  obtain ⟨cFM, cBM, _qF, _qB, jM, h⟩ := hdata
  rcases h with ⟨_hCF, _hCB, _hClosed, _hF, _hB, _hCFmap, _hCBmap,
    _hChart, _hTriangle, k, hk, Ek, _hEk, hPk, hOld, hModels⟩
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let EP : cFN.pt ≅ genericScalarModel S P.hom := hP.flip.isoOverPullback
  let qPk : cFN.pt.left ⟶ (stageScalarModel S P.hom k).left :=
    EP.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)
  let q := fun i => Classical.choose (hModels i)
  refine ⟨k, hk, (fun i => stageScalarModel S (cBM i).pt.hom k),
    (fun i => chosenScalarArrow κ (jM i) ≫ Ek.hom), qPk, q, hPk, hOld, ?_⟩
  intro i
  rcases Classical.choose_spec (hModels i) with
    ⟨hClosed, hCart, hTriangle, _hOriginal, hfp, hcompact, hqs⟩
  exact ⟨hClosed, hCart, hTriangle, hfp, hcompact, hqs⟩

end SchubertGeometry
