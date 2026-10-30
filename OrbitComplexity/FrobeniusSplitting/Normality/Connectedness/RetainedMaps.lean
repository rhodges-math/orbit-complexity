import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Mathlib.Data.Fintype.Basic

/-!
# Retaining a finite family of specified morphisms jointly

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u v

private theorem retained_maps_bound {I J : Type*} [Fintype I] [Preorder J]
    [IsDirectedOrder J] (i : I → J) (start : J) :
    ∃ j : J, start ≤ j ∧ ∀ r, i r ≤ j := by
  classical
  have h : ∀ s : Finset I, ∃ j : J, start ≤ j ∧ ∀ r ∈ s, i r ≤ j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨start, le_rfl, by intro r hr; simp at hr⟩
    | @insert r s _ ih =>
      obtain ⟨j, hstart, hj⟩ := ih
      obtain ⟨k, hjk, hrk⟩ := exists_ge_ge j (i r)
      refine ⟨k, hstart.trans hjk, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hrk
      · exact (hj t ht).trans hjk
  obtain ⟨j, hj, hall⟩ := h Finset.univ
  exact ⟨j, hj, fun r => hall r (Finset.mem_univ r)⟩

/-- A finite family of specified generic morphisms descends jointly above any
given coefficient stage, between scalar pullbacks of the same original models. -/
theorem exists_retained_maps
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (X Y : I → Scheme.{u})
    [∀ i, CompactSpace (X i)] [∀ i, QuasiSeparatedSpace (X i)]
    (a : ∀ i, X i ⟶ Spec (.of S)) (b : ∀ i, Y i ⟶ Spec (.of S))
    [∀ i, LocallyOfFinitePresentation (b i)]
    (g : ∀ i, genericScalarModel S (a i) ⟶ genericScalarModel S (b i))
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (f : ∀ i, stageScalarModel S (a i) j ⟶ stageScalarModel S (b i) j),
      ∀ i, (modelScalarCone S (a i)).π.app (op j) ≫ (f i).left =
        (g i).left ≫ (modelScalarCone S (b i)).π.app (op j) := by
  classical
  choose j fj hfj using fun i => exists_model_morphism S hS (a i) (b i) (g i)
  obtain ⟨k, hstart, hjk⟩ := retained_maps_bound j start
  let f (i : I) := extendModelMorphism S (a i) (b i) (hjk i) (fj i)
  refine ⟨k, hstart, f, ?_⟩
  intro i
  exact extendModelMorphism_baseChange S (a i) (b i) (hjk i) (fj i) (g i) (hfj i)

end FrobeniusSplitting
