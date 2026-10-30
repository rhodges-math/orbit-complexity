import OrbitComplexity.FrobeniusSplitting.Normality.Covers.JointOpenData
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.OpenDenominatorModels

/-! # Open models retaining parameters and both chosen scalar-extension comparisons -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w z
namespace FrobeniusSplitting

/-- Chosen coordinate models retain finite parameters, all open maps and generic pushouts. -/
theorem exists_joint_open_models {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (M : C ⥤ CommAlgCat.{u} S)
    [∀ i, Algebra.FinitePresentation S (M.obj i)] [∀ i, Algebra.Smooth S (M.obj i)]
    (F : C ⥤ CommAlgCat.{u} K) (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i)
    (he : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e i).toAlgHom)
    (hopen : ∀ i j (f : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)))
    (V : C → Type z) [∀ i, Finite (V i)] (values : ∀ i, V i → F.obj i) :
    jointOpenModelSpec S M F e V values := by
  classical
  dsimp only [jointOpenModelSpec]
  have H := exists_open_denominator_models S hS M F e he hopen V values
  rcases H with ⟨L, hL, a, hcover, hlocal, T, hST, P, eP, d, hd,
    hT, hfp, hsm, heval, hvalues, hP, ⟨g, hg⟩, hu⟩
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let N := modelFunctor (fun i ↦ P i) (F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    d (fun i ↦ (P i).val.toRingHom) (fun _ ↦ Subtype.val_injective) hd
  let (i : C) : Algebra.FinitePresentation T (N.obj i) := hfp i
  let (i : C) : Algebra.Smooth T (N.obj i) := hsm i
  have heP (i j : C) (f : i ⟶ j) : (eP j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (eP i).toAlgHom := by
    ext z
    change eP j ((1 : K) ⊗ₜ[T] d f z) =
      (F.map f).hom (eP i ((1 : K) ⊗ₜ[T] z))
    rw [heval, heval]
    exact hd i j f z
  let (b : Σ i : C, Σ j : C, i ⟶ j) : Finite (L b) := hL b
  have Hopen := exists_chosen_open_models T hT N F eP heP L a g hcover hlocal hg
  exact ⟨L, hL, a, hcover, hlocal, T, hST, P, eP, d, hd, hT, hfp, hsm,
    heval, hvalues, hP, ⟨g, hg⟩, hu, Hopen⟩

end FrobeniusSplitting
