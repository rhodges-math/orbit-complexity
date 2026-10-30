import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Cartesian comparison diagrams for affine models
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

variable {C : Type v} [Category.{w} C] {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (D₀ : C ⥤ CommAlgCat.{u} R) (D : C ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i)
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)

private def comparisonMap (i : C) : D₀.obj i →+* D.obj i :=
  (e i).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

/-- Natural scalar comparisons define a morphism from generic affine diagrams to their models. -/
noncomputable def affineModelNatTrans :
    D.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K)) ⟶
      D₀.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)) where
  app i := Spec.map (CommRingCat.ofHom (comparisonMap D₀ D e i.unop))
  naturality {i j} f := by
    change Spec.map (CommRingCat.ofHom (D.map f.unop).hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (comparisonMap D₀ D e j.unop)) =
      Spec.map (CommRingCat.ofHom (comparisonMap D₀ D e i.unop)) ≫
        Spec.map (CommRingCat.ofHom (D₀.map f.unop).hom.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    apply RingHom.ext
    intro m
    have h := AlgHom.congr_fun (hnatural j.unop i.unop f.unop) ((1 : K) ⊗ₜ[R] m)
    change e i.unop ((1 : K) ⊗ₜ[R] (D₀.map f.unop).hom m) =
      (D.map f.unop).hom (e j.unop ((1 : K) ⊗ₜ[R] m)) at h
    exact h.symm

/-- The comparison between generic affine diagrams and their models is cartesian on every arrow. -/
theorem affineModel_equifibered : (affineModelNatTrans D₀ D e hnatural).Equifibered := by
  let (i : C) : Algebra R (D.obj i) :=
    ((algebraMap K (D.obj i)).comp (algebraMap R K)).toAlgebra
  have (i : C) : IsScalarTower R K (D.obj i) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro i j f
  let F := D.op ⋙ algSpec (.of K)
  let G := D₀.op ⋙ algSpec (.of R)
  let α := affineModelNatTrans D₀ D e hnatural
  have hj : CategoryTheory.IsPullback (α.app j) (F.obj j).hom (G.obj j).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (isPullback_affineModel (e j.unop)).flip
  have hi : CategoryTheory.IsPullback (α.app i)
      ((F.map f).left ≫ (F.obj j).hom) ((G.map f).left ≫ (G.obj j).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [Over.w, Over.w]
    exact (isPullback_affineModel (e i.unop)).flip
  exact (hi.of_bot (α.naturality f).symm hj).flip

end FrobeniusSplitting
