import OrbitComplexity.FrobeniusSplitting.Normality.ModelGraphs
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Arithmetic models of finite diagrams

Subalgebra models preserve identities and compositions through their inclusions. Consequently
a finite diagram descends to a functor, with natural scalar-extension comparisons and smooth
models for any selected smooth objects.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

open CategoryTheory

universe u v w

/-- A finite diagram admits finitely presented arithmetic models preserving smoothness
on selected objects, with natural scalar-extension comparisons. -/
theorem exists_arithmetic_functor_smooth_on {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (D : C ⥤ CommAlgCat.{u} K) [∀ i, Algebra.FinitePresentation K (D.obj i)]
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (D.obj i)) :
    ∃ (R : Subalgebra ℤ K) (D₀ : C ⥤ CommAlgCat.{u} R)
      (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (D₀.obj i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (D₀.obj i)) ∧
      ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
        (D.map f).hom.comp (e i).toAlgHom := by
  classical
  let arrows := Σ i : C, Σ j : C, i ⟶ j
  let src (a : arrows) := a.1
  let tgt (a : arrows) := a.2.1
  let f (a : arrows) : D.obj (src a) →ₐ[K] D.obj (tgt a) := (D.map a.2.2).hom
  obtain ⟨R, hfg, models, e, hfp, hsmModel, he, hmaps⟩ :=
    exists_arithmetic_graph_smooth_on (fun i ↦ (D.obj i : Type u)) smoothNodes hsm src tgt f
  let fm {i j : C} (g : i ⟶ j) : models i →ₐ[R] models j :=
    (((D.map g).hom.restrictScalars R).comp (models i).val).codRestrict (models j)
      (fun x ↦ hmaps ⟨i, j, g⟩ x.property)
  let D₀ : C ⥤ CommAlgCat.{u} R :=
    { obj := fun i ↦ CommAlgCat.of R (models i)
      map := fun g ↦ CommAlgCat.ofHom (fm g)
      map_id := by
        intro i
        ext x
        change (D.map (𝟙 i)).hom (x : D.obj i) = (x : D.obj i)
        rw [D.map_id, CommAlgCat.hom_id, AlgHom.id_apply]
      map_comp := by
        intro i j k g h
        ext x
        change (D.map (g ≫ h)).hom (x : D.obj i) =
          (D.map h).hom ((D.map g).hom (x : D.obj i))
        rw [D.map_comp, CommAlgCat.hom_comp, AlgHom.comp_apply] }
  refine ⟨R, D₀, e, hfg, hfp, hsmModel, fun i j g ↦ ?_⟩
  ext x
  change e j ((1 : K) ⊗ₜ[R] fm g x) = (D.map g).hom (e i ((1 : K) ⊗ₜ[R] x))
  rw [he, he]
  simp only [map_one, one_mul]
  rfl

end FrobeniusSplitting
