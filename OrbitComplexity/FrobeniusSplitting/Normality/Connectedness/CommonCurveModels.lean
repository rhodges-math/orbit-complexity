import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.EndpointModels

/-!
# Both endpoints on a common retained curve

After finite simultaneous scalar descent, the two endpoint triangles use one
curve arrow for each edge. Their anchors remain extensions of the specified
initial anchor arrows.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u v

/-- Both endpoints of each member of a finite curve family descend with one
common curve map and with incidence to the same specified anchor models. -/
theorem exists_common_curve_models
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (P : I → Scheme.{u})
    [∀ r : I, CompactSpace (P r)] [∀ r : I, QuasiSeparatedSpace (P r)]
    (p : ∀ r : I, P r ⟶ Spec (.of S))
    [∀ r : I, LocallyOfFinitePresentation (p r)]
    {D : Scheme.{u}} (d : D ⟶ Spec (.of S)) [LocallyOfFinitePresentation d]
    (sK : ∀ r : I × Bool, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (p r.1))
    (cK : ∀ r : I, genericScalarModel S (p r) ⟶ genericScalarModel S d)
    (aK : ∀ _r : I × Bool, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S d)
    (he : ∀ r : I × Bool, sK r ≫ cK r.1 = aK r) (i : CoefficientStage S)
    (a : ∀ _r : I × Bool, stageScalarModel S (𝟙 (Spec (.of S))) i ⟶
      stageScalarModel S d i)
    (ha : ∀ r : I × Bool,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (a r).left =
        (aK r).left ≫ (modelScalarCone S d).π.app (op i)) :
    ∃ (l : CoefficientStage S) (hil : i ≤ l)
      (j : CoefficientStage S) (hlj : l ≤ j)
      (k : CoefficientStage S) (hjk : j ≤ k)
      (s : ∀ r : I × Bool, stageScalarModel S (𝟙 (Spec (.of S))) k ⟶
        stageScalarModel S (p r.1) k)
      (c : ∀ r : I, stageScalarModel S (p r) k ⟶ stageScalarModel S d k),
      ∀ r : I × Bool,
      s r ≫ c r.1 = extendModelMorphism S (𝟙 (Spec (.of S))) d hjk
        (extendModelMorphism S (𝟙 (Spec (.of S))) d hlj
          (extendModelMorphism S (𝟙 (Spec (.of S))) d hil (a r))) ∧
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op k) ≫ (s r).left =
        (sK r).left ≫ (modelScalarCone S (p r.1)).π.app (op k) ∧
      (modelScalarCone S (p r.1)).π.app (op k) ≫ (c r.1).left =
        (cK r.1).left ≫ (modelScalarCone S d).π.app (op k) := by
  obtain ⟨l, hil, j, hlj, s, c, h⟩ := exists_endpoint_models S hS
    (fun r : I × Bool => P r.1) (fun r => p r.1) d
    sK (fun r => cK r.1) aK he i a ha
  let aJ : ∀ _r : I × Bool, stageScalarModel S (𝟙 (Spec (.of S))) j ⟶
      stageScalarModel S d j := fun r =>
    extendModelMorphism S (𝟙 _) d hlj (extendModelMorphism S (𝟙 _) d hil (a r))
  have haL : ∀ r : I × Bool,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op l) ≫
          (extendModelMorphism S (𝟙 _) d hil (a r)).left =
        (aK r).left ≫ (modelScalarCone S d).π.app (op l) := fun r =>
    extendModelMorphism_baseChange S (𝟙 _) d hil (a r) (aK r) (ha r)
  have haJ : ∀ r : I × Bool,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op j) ≫ (aJ r).left =
        (aK r).left ≫ (modelScalarCone S d).π.app (op j) := fun r =>
    extendModelMorphism_baseChange S (𝟙 _) d hlj _ (aK r) (haL r)
  obtain ⟨k, hjk, hk⟩ := exists_retained_triangles S hS
    (fun r : I × Bool => P r.1) (fun r => p r.1) d
    sK (fun r => cK r.1) aK he j s (fun r => c (r.1, false)) aJ
    (fun r => (h r).2.1) (fun r => (h (r.1, false)).2.2) haJ
  refine ⟨l, hil, j, hlj, k, hjk,
    (fun r => extendModelMorphism S (𝟙 _) (p r.1) hjk (s r)),
    (fun r => extendModelMorphism S (p r) d hjk (c (r, false))), fun r => ?_⟩
  exact ⟨hk r,
    extendModelMorphism_baseChange S (𝟙 _) (p r.1) hjk (s r) (sK r) (h r).2.1,
    extendModelMorphism_baseChange S (p r.1) d hjk (c (r.1, false))
      (cK r.1) (h (r.1, false)).2.2⟩

end FrobeniusSplitting
