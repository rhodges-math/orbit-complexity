import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.DiagramMaps
import OrbitComplexity.FrobeniusSplitting.Normality.NaturalComparisons
import Mathlib.CategoryTheory.Sums.Basic

/-!
# Arithmetic models of natural transformations
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A natural transformation between finite open algebra diagrams descends with the diagrams. -/
theorem exists_natural_open_models {C D : Type u} [Category.{u} C] [Category.{u} D]
    [Finite C] [Finite D] [∀ i j : C, Finite (i ⟶ j)] [∀ i j : D, Finite (i ⟶ j)]
    {K : Type u} [CommRing K] (F : C ⥤ CommAlgCat.{u} K) (G : D ⥤ CommAlgCat.{u} K)
    [∀ i, Algebra.FinitePresentation K (F.obj i)]
    [∀ i, Algebra.FinitePresentation K (G.obj i)]
    (hFopen : ∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)))
    (hGopen : ∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (G.map f).hom.toRingHom)))
    (H : C ⥤ D) (α : H ⋙ G ⟶ F)
    (smoothNodes : Set (C ⊕ D))
    (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K ((F.sum' G).obj i)) :
    ∃ (R : Subalgebra ℤ K) (D₀ : C ⊕ D ⥤ CommAlgCat.{u} R)
      (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] (F.sum' G).obj i)
      (β : H ⋙ (Sum.inr_ C D ⋙ D₀) ⟶ Sum.inl_ C D ⋙ D₀),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (D₀.obj i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (D₀.obj i)) ∧
      (∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
        ((F.sum' G).map f).hom.comp (e i).toAlgHom) ∧
      (∀ i, Function.Injective (fun x : D₀.obj i ↦ e i ((1 : K) ⊗ₜ[R] x))) ∧
      (∀ i, (e (.inl i)).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (β.app i).hom) =
        (α.app i).hom.comp (e (.inr (H.obj i))).toAlgHom) ∧
      (∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (D₀.map f).hom.toRingHom))) ∧
      ∀ (i j k l : C ⊕ D) (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
        CategoryTheory.IsPushout (CommRingCat.ofHom ((F.sum' G).map f).hom.toRingHom)
          (CommRingCat.ofHom ((F.sum' G).map g).hom.toRingHom)
          (CommRingCat.ofHom ((F.sum' G).map p).hom.toRingHom)
          (CommRingCat.ofHom ((F.sum' G).map q).hom.toRingHom) →
        CategoryTheory.IsPushout (CommRingCat.ofHom (D₀.map f).hom.toRingHom)
          (CommRingCat.ofHom (D₀.map g).hom.toRingHom)
          (CommRingCat.ofHom (D₀.map p).hom.toRingHom)
          (CommRingCat.ofHom (D₀.map q).hom.toRingHom) := by
  classical
  have (i j : C ⊕ D) : Finite (i ⟶ j) := by
    rcases i with i | i <;> rcases j with j | j
    · exact inferInstanceAs (Finite (ULift.{u} (i ⟶ j)))
    · change Finite PEmpty
      infer_instance
    · change Finite PEmpty
      infer_instance
    · exact inferInstanceAs (Finite (ULift.{u} (i ⟶ j)))
  have (i : C ⊕ D) : Algebra.FinitePresentation K ((F.sum' G).obj i) := by
    rcases i with i | i
    · exact inferInstanceAs (Algebra.FinitePresentation K (F.obj i))
    · exact inferInstanceAs (Algebra.FinitePresentation K (G.obj i))
  have hopen : ∀ i j (f : i ⟶ j), AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((F.sum' G).map f).hom.toRingHom)) := by
    intro i j f
    exact Sum.homInduction (fun i j f ↦ hFopen i j f) (fun i j f ↦ hGopen i j f) f
  obtain ⟨R, D₀, e, φ, hfg, hfp, hsmooth, hnatural, hinj, hφ, hopen₀, hpush⟩ :=
    exists_open_diagram_maps (F.sum' G) hopen smoothNodes hsm
      (fun i : C ↦ Sum.inr (H.obj i)) (fun i ↦ Sum.inl i) (fun i ↦ (α.app i).hom)
  let β : H ⋙ (Sum.inr_ C D ⋙ D₀) ⟶ Sum.inl_ C D ⋙ D₀ :=
    naturalMapOfComparison H (Sum.inl_ C D ⋙ D₀) (Sum.inr_ C D ⋙ D₀) F G
      (fun i ↦ e (.inl i)) (fun i ↦ e (.inr i))
      (fun i j f ↦ hnatural _ _ ((Sum.inl_ C D).map f))
      (fun i j f ↦ hnatural _ _ ((Sum.inr_ C D).map f))
      (fun i ↦ hinj (.inl i)) α φ hφ
  exact ⟨R, D₀, e, β, hfg, hfp, hsmooth, hnatural, hinj, hφ, hopen₀, hpush⟩

end FrobeniusSplitting
