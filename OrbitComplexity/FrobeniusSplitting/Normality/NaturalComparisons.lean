import Batteries.Tactic.Lint
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reflection of naturality by scalar comparisons
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

/-- Injective scalar comparisons reflect the naturality of a family of algebra maps. -/
noncomputable def naturalMapOfComparison
    {C : Type v} [Category.{w} C] {D : Type v} [Category.{w} D]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (H : C ⥤ D) (F₀ : C ⥤ CommAlgCat.{u} R) (G₀ : D ⥤ CommAlgCat.{u} R)
    (F : C ⥤ CommAlgCat.{u} K) (G : D ⥤ CommAlgCat.{u} K)
    (eF : ∀ i, K ⊗[R] F₀.obj i ≃ₐ[K] F.obj i)
    (eG : ∀ i, K ⊗[R] G₀.obj i ≃ₐ[K] G.obj i)
    (hF : ∀ i j (f : i ⟶ j), (eF j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (F₀.map f).hom) =
      (F.map f).hom.comp (eF i).toAlgHom)
    (hG : ∀ i j (f : i ⟶ j), (eG j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (G₀.map f).hom) =
      (G.map f).hom.comp (eG i).toAlgHom)
    (hinj : ∀ i, Function.Injective (fun x : F₀.obj i ↦ eF i ((1 : K) ⊗ₜ[R] x)))
    (α : H ⋙ G ⟶ F) (φ : ∀ i, G₀.obj (H.obj i) →ₐ[R] F₀.obj i)
    (hφ : ∀ i, (eF i).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (φ i)) =
      (α.app i).hom.comp (eG (H.obj i)).toAlgHom) : H ⋙ G₀ ⟶ F₀ where
  app i := CommAlgCat.ofHom (φ i)
  naturality i j f := by
    have evF (x : F₀.obj i) :
        eF j ((1 : K) ⊗ₜ[R] (F₀.map f).hom x) =
          (F.map f).hom (eF i ((1 : K) ⊗ₜ[R] x)) := by
      simpa using AlgHom.congr_fun (hF i j f) ((1 : K) ⊗ₜ[R] x)
    have evG (x : G₀.obj (H.obj i)) :
        eG (H.obj j) ((1 : K) ⊗ₜ[R] (G₀.map (H.map f)).hom x) =
          (G.map (H.map f)).hom (eG (H.obj i) ((1 : K) ⊗ₜ[R] x)) := by
      simpa using AlgHom.congr_fun (hG _ _ (H.map f)) ((1 : K) ⊗ₜ[R] x)
    have evφ (i : C) (x : G₀.obj (H.obj i)) :
        eF i ((1 : K) ⊗ₜ[R] φ i x) =
          (α.app i).hom (eG (H.obj i) ((1 : K) ⊗ₜ[R] x)) := by
      simpa using AlgHom.congr_fun (hφ i) ((1 : K) ⊗ₜ[R] x)
    ext x
    apply hinj j
    change eF j ((1 : K) ⊗ₜ[R] φ j ((G₀.map (H.map f)).hom x)) =
      eF j ((1 : K) ⊗ₜ[R] (F₀.map f).hom (φ i x))
    rw [evφ, evG, evF, evφ]
    exact congrArg (fun q ↦ q.hom (eG (H.obj i) ((1 : K) ⊗ₜ[R] x)))
      (α.naturality f)

end FrobeniusSplitting
