import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageSections

/-!
# Finite simultaneous retention of sections

A finite family of sections of generic scalar models descends to a common
coefficient stage. The comparison retains the specified section morphisms.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u v

private def section_arrow {T : Type*} [Category T] {B : T} (U P : Over B)
    (s : B ⟶ P.left) (hs : s ≫ P.hom = 𝟙 B) : U ⟶ P :=
  Over.homMk (U.hom ≫ s) (by rw [Category.assoc, hs, Category.comp_id])

private theorem section_arrow_comparison {T : Type*} [Category T] {B V W : T}
    (U P : Over B) (s : B ⟶ P.left) (hs : s ≫ P.hom = 𝟙 B)
    {g : U ⟶ P} (hg : g = section_arrow U P s hs)
    (L : U.left ⟶ V) (f : V ⟶ W) (q : P.left ⟶ W)
    (h : L ≫ f = g.left ≫ q) : L ≫ f = U.hom ≫ s ≫ q := by
  subst g
  exact h.trans (Category.assoc _ _ _)

private theorem section_comp_base {T : Type*} [Category T] {B : T}
    {U P : Over B} (s : B ⟶ U.left) (hs : s ≫ U.hom = 𝟙 B) (f : U ⟶ P) :
    (s ≫ f.left) ≫ P.hom = 𝟙 B := by
  rw [Category.assoc, f.w, hs]

private theorem section_comparison {T : Type*} [Category T]
    {B C U V P W : T} (κ : B ⟶ C) (s₀ : C ⟶ V) (s : B ⟶ U)
    (b : U ⟶ B) (L : U ⟶ V) (f : V ⟶ W) (t : B ⟶ P) (q : P ⟶ W)
    (hκ : κ ≫ s₀ = s ≫ L) (hs : s ≫ b = 𝟙 B)
    (hf : L ≫ f = b ≫ t ≫ q) : κ ≫ (s₀ ≫ f) = t ≫ q := by
  rw [← Category.assoc, hκ, Category.assoc, hf, ← Category.assoc,
    hs, Category.id_comp]

/-- Finitely many generic sections retain their section and comparison equations
at one coefficient stage above a specified starting stage. -/
theorem exists_retained_sections
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (X : I → Scheme.{u})
    (a : ∀ r : I, X r ⟶ Spec (.of S))
    [∀ r : I, LocallyOfFinitePresentation (a r)]
    (s : ∀ r : I, Spec (.of K) ⟶ (genericScalarModel S (a r)).left)
    (hs : ∀ r : I, s r ≫ (genericScalarModel S (a r)).hom = 𝟙 _)
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (f : ∀ r : I, stageScalarModel S (𝟙 (Spec (.of S))) j ⟶
        stageScalarModel S (a r) j), ∀ r : I,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op j) ≫ (f r).left =
        (genericScalarModel S (𝟙 (Spec (.of S)))).hom ≫ s r ≫
          (modelScalarCone S (a r)).π.app (op j) ∧
      (stageOriginSection S (𝟙 _) (𝟙 _) (Category.id_comp _) j ≫ (f r).left) ≫
          (stageScalarModel S (a r) j).hom = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap j.val K)) ≫
          (stageOriginSection S (𝟙 _) (𝟙 _) (Category.id_comp _) j ≫ (f r).left) =
        s r ≫ (modelScalarCone S (a r)).π.app (op j) := by
  let g : ∀ r : I, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (a r) := fun r =>
    section_arrow _ _ (s r) (hs r)
  obtain ⟨j, hj, f, hf⟩ := exists_retained_maps S hS (fun _ : I => Spec (.of S)) X
    (fun _ => 𝟙 _) a g start
  refine ⟨j, hj, f, fun r => ?_⟩
  have hr := section_arrow_comparison _ _ (s r) (hs r) (g := g r) rfl
    _ _ _ (hf r)
  refine ⟨hr, section_comp_base _
    (stageOriginSection_base S (𝟙 _) (𝟙 _) (Category.id_comp _) j) (f r), ?_⟩
  exact section_comparison _ _ _ _ _ _ _ _
    (stageOriginSection_comparison S (𝟙 _) (𝟙 _) (Category.id_comp _) j)
    (pullbackSection_base _ _ _ _) hr

end FrobeniusSplitting
