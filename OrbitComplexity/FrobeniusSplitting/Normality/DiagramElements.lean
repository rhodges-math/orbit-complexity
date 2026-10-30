import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PresentationGraphs
import Mathlib.Algebra.Category.CommAlgCat.Basic
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteModels

/-!
# Diagram Elements

Finite diagrams descend with selected smooth objects and chosen elements.
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

/-- Finite diagrams descend with selected smooth objects and lifts of finitely many elements. -/
theorem exists_arithmetic_diagram_elements {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (D : C ⥤ CommAlgCat.{u} K) [∀ i, Algebra.FinitePresentation K (D.obj i)]
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (D.obj i))
    (J : C → Type*) [∀ i, Finite (J i)] (a : ∀ i, J i → D.obj i) :
    ∃ (R : Subalgebra ℤ K) (D₀ : C ⥤ CommAlgCat.{u} R)
      (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (D₀.obj i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (D₀.obj i)) ∧
      (∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
        (D.map f).hom.comp (e i).toAlgHom) ∧
      ∃ a₀ : ∀ i, J i → D₀.obj i, ∀ i j, e i ((1 : K) ⊗ₜ[R] a₀ i j) = a i j := by
  classical
  obtain ⟨S, hS, hmodels⟩ := exists_models_smooth_on
    (fun i ↦ (D.obj i : Type u)) smoothNodes hsm
  choose M ringM algM fpM smoothM comparison using hmodels
  let (i : C) : CommRing (M i) := ringM i
  let (i : C) : Algebra S (M i) := algM i
  have (i : C) : Algebra.FinitePresentation S (M i) := fpM i
  let e (i : C) := (comparison i).some
  let vars (i : C) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M i))
  let rels (i : C) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M i))
  let Q (i : C) : Algebra.Presentation S (M i) (vars i) (rels i) :=
    Algebra.Presentation.ofFinitePresentation S (M i)
  let arrows := Σ i : C, Σ j : C, i ⟶ j
  let src (b : arrows) := b.1
  let tgt (b : arrows) := b.2.1
  let maps (b : arrows) : D.obj (src b) →ₐ[K] D.obj (tgt b) := (D.map b.2.2).hom
  obtain ⟨R, _, models, comparison, _, hfg, _, hfp, hsmooth, heval, hmaps, helts⟩ :=
    exists_presentation_image_graph S hS M (fun i ↦ (D.obj i : Type u)) vars rels Q e
      smoothNodes smoothM src tgt maps J a
  let fm {i j : C} (f : i ⟶ j) : models i →ₐ[R] models j :=
    (((D.map f).hom.restrictScalars R).comp (models i).val).codRestrict (models j)
      (fun x ↦ hmaps ⟨i, j, f⟩ x.property)
  let D₀ : C ⥤ CommAlgCat.{u} R :=
    { obj := fun i ↦ CommAlgCat.of R (models i)
      map := fun f ↦ CommAlgCat.ofHom (fm f)
      map_id := by
        intro i
        ext x
        change (D.map (𝟙 i)).hom x.val = x.val
        exact AlgHom.congr_fun
          (congrArg (fun t : D.obj i ⟶ D.obj i ↦ t.hom) (D.map_id i)) x.val
      map_comp := by
        intro i j k f g
        ext x
        change (D.map (f ≫ g)).hom x.val = (D.map g).hom ((D.map f).hom x.val)
        exact AlgHom.congr_fun
          (congrArg (fun t : D.obj i ⟶ D.obj k ↦ t.hom) (D.map_comp f g)) x.val }
  refine ⟨R, D₀, comparison, hfg, hfp, hsmooth, ?_,
    (fun i j ↦ ⟨a i j, helts i j⟩), ?_⟩
  · intro i j f
    ext x
    change comparison j ((1 : K) ⊗ₜ[R] fm f x) =
      (D.map f).hom (comparison i ((1 : K) ⊗ₜ[R] x))
    rw [heval, heval]
    simp only [map_one, one_mul]
    rfl
  · intro i j
    rw [heval]
    simp only [map_one, one_mul]

end FrobeniusSplitting
