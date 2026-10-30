import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.EndpointEquations

/-!
# Common scalar models for curves and their endpoints

The endpoint arrows and curve arrows descend together with their incidence to
an existing finite family of anchor arrows. The anchor arrows remain extensions
of the same specified models, including their special fibres.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u v

/-- Curve maps and endpoint maps admit a common finite scalar stage where their
composites equal the extensions of the specified anchor maps. -/
theorem exists_endpoint_models
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (P : I → Scheme.{u})
    [∀ r : I, CompactSpace (P r)] [∀ r : I, QuasiSeparatedSpace (P r)]
    (p : ∀ r : I, P r ⟶ Spec (.of S))
    [∀ r : I, LocallyOfFinitePresentation (p r)]
    {D : Scheme.{u}} (d : D ⟶ Spec (.of S)) [LocallyOfFinitePresentation d]
    (sK : ∀ r : I, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (p r))
    (cK : ∀ r : I, genericScalarModel S (p r) ⟶ genericScalarModel S d)
    (aK : ∀ _r : I, genericScalarModel S (𝟙 (Spec (.of S))) ⟶ genericScalarModel S d)
    (he : ∀ r : I, sK r ≫ cK r = aK r) (i : CoefficientStage S)
    (a : ∀ _r : I, stageScalarModel S (𝟙 (Spec (.of S))) i ⟶ stageScalarModel S d i)
    (ha : ∀ r : I, (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (a r).left =
      (aK r).left ≫ (modelScalarCone S d).π.app (op i)) :
    ∃ (l : CoefficientStage S) (hil : i ≤ l)
      (j : CoefficientStage S) (hlj : l ≤ j)
      (s : ∀ r : I, stageScalarModel S (𝟙 (Spec (.of S))) j ⟶ stageScalarModel S (p r) j)
      (c : ∀ r : I, stageScalarModel S (p r) j ⟶ stageScalarModel S d j), ∀ r : I,
      s r ≫ c r = extendModelMorphism S (𝟙 (Spec (.of S))) d hlj
        (extendModelMorphism S (𝟙 (Spec (.of S))) d hil (a r)) ∧
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op j) ≫ (s r).left =
        (sK r).left ≫ (modelScalarCone S (p r)).π.app (op j) ∧
      (modelScalarCone S (p r)).π.app (op j) ≫ (c r).left =
        (cK r).left ≫ (modelScalarCone S d).π.app (op j) := by
  obtain ⟨k, hik, c, hc⟩ := exists_retained_maps S hS P (fun _ : I => D)
    p (fun _ => d) cK i
  obtain ⟨l, hkl, s, hs⟩ := exists_retained_maps S hS (fun _ : I => Spec (.of S)) P
    (fun _ => 𝟙 _) p sK k
  let hil : i ≤ l := hik.trans hkl
  let c₁ : ∀ r : I, stageScalarModel S (p r) l ⟶ stageScalarModel S d l :=
    fun r => extendModelMorphism S (p r) d hkl (c r)
  let a₁ : ∀ _r : I, stageScalarModel S (𝟙 (Spec (.of S))) l ⟶ stageScalarModel S d l :=
    fun r => extendModelMorphism S (𝟙 _) d hil (a r)
  have hc₁ : ∀ r : I, (modelScalarCone S (p r)).π.app (op l) ≫ (c₁ r).left =
      (cK r).left ≫ (modelScalarCone S d).π.app (op l) := fun r =>
    extendModelMorphism_baseChange S (p r) d hkl (c r) (cK r) (hc r)
  have ha₁ : ∀ r : I, (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op l) ≫ (a₁ r).left =
      (aK r).left ≫ (modelScalarCone S d).π.app (op l) := fun r =>
    extendModelMorphism_baseChange S (𝟙 _) d hil (a r) (aK r) (ha r)
  obtain ⟨j, hlj, hj⟩ := exists_retained_triangles S hS P p d sK cK aK he l s c₁ a₁ hs hc₁ ha₁
  refine ⟨l, hil, j, hlj, (fun r => extendModelMorphism S (𝟙 _) (p r) hlj (s r)),
    (fun r => extendModelMorphism S (p r) d hlj (c₁ r)), fun r => ?_⟩
  exact ⟨hj r,
    extendModelMorphism_baseChange S (𝟙 _) (p r) hlj (s r) (sK r) (hs r),
    extendModelMorphism_baseChange S (p r) d hlj (c₁ r) (cK r) (hc₁ r)⟩

end FrobeniusSplitting
