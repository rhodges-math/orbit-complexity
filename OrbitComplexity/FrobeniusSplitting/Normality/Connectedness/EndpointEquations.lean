import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageEquations

/-!
# Simultaneous retention of endpoint incidence

Finite scalar descent retains a commuting section-curve-anchor triangle.
Extending its section and curve separately preserves their composition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u v

private theorem cartesian_comp {T : Type*} [Category T] {B B' : T}
    {X Y Z : Over B} {X' Y' Z' : Over B'}
    (κ : B' ⟶ B) (tx : X'.left ⟶ X.left) (ty : Y'.left ⟶ Y.left)
    (tz : Z'.left ⟶ Z.left) (hz : IsPullback tz Z'.hom Z.hom κ)
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : X' ⟶ Z')
    (hf : f'.left ≫ ty = tx ≫ f.left)
    (hg : g'.left ≫ tz = ty ≫ g.left)
    (hh : h'.left ≫ tz = tx ≫ (f ≫ g).left) : h' = f' ≫ g' := by
  apply Over.OverMorphism.ext
  apply hz.hom_ext
  · change h'.left ≫ tz = (f'.left ≫ g'.left) ≫ tz
    rw [hh, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
    rfl
  · exact h'.w.trans (f' ≫ g').w.symm

private theorem extended_comp {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y Z : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    (c : Z ⟶ Spec (.of S)) {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : stageScalarModel S b i ⟶ stageScalarModel S c i) :
    extendModelMorphism S a c hij (f ≫ g) =
      extendModelMorphism S a b hij f ≫ extendModelMorphism S b c hij g :=
  cartesian_comp _ _ _ _ (stageScalarCartesian S c hij) f g _ _ _
    (extendModelMorphism_transition S a b hij f)
    (extendModelMorphism_transition S b c hij g)
    (extendModelMorphism_transition S a c hij (f ≫ g))

private theorem triangle_comparison {T : Type*} [Category T] {B B' : T}
    {U P D : Over B} {U' P' D' : Over B'}
    (LU : U.left ⟶ U'.left) (LP : P.left ⟶ P'.left) (LD : D.left ⟶ D'.left)
    (s : U ⟶ P) (c : P ⟶ D) (a : U ⟶ D)
    (s' : U' ⟶ P') (c' : P' ⟶ D') (a' : U' ⟶ D')
    (hs : LU ≫ s'.left = s.left ≫ LP)
    (hc : LP ≫ c'.left = c.left ≫ LD)
    (ha : LU ≫ a'.left = a.left ≫ LD) (he : s ≫ c = a) :
    LU ≫ (s' ≫ c').left = LU ≫ a'.left := by
  change LU ≫ (s'.left ≫ c'.left) = _
  rw [← Category.assoc, hs, Category.assoc, hc, ← Category.assoc]
  exact (congrArg (fun f : U ⟶ D => f.left ≫ LD) he).trans ha.symm

/-- Finite endpoint triangles that commute after generic scalar extension commute
at one common later stage, with each arrow extended from the same chosen models. -/
theorem exists_retained_triangles
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (P : I → Scheme.{u})
    (p : ∀ r : I, P r ⟶ Spec (.of S))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of S)) [LocallyOfFiniteType d]
    (sK : ∀ r : I, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (p r))
    (cK : ∀ r : I, genericScalarModel S (p r) ⟶ genericScalarModel S d)
    (aK : ∀ _r : I, genericScalarModel S (𝟙 (Spec (.of S))) ⟶ genericScalarModel S d)
    (he : ∀ r : I, sK r ≫ cK r = aK r) (i : CoefficientStage S)
    (s : ∀ r : I, stageScalarModel S (𝟙 (Spec (.of S))) i ⟶ stageScalarModel S (p r) i)
    (c : ∀ r : I, stageScalarModel S (p r) i ⟶ stageScalarModel S d i)
    (a : ∀ _r : I, stageScalarModel S (𝟙 (Spec (.of S))) i ⟶ stageScalarModel S d i)
    (hs : ∀ r : I, (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (s r).left =
      (sK r).left ≫ (modelScalarCone S (p r)).π.app (op i))
    (hc : ∀ r : I, (modelScalarCone S (p r)).π.app (op i) ≫ (c r).left =
      (cK r).left ≫ (modelScalarCone S d).π.app (op i))
    (ha : ∀ r : I, (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (a r).left =
      (aK r).left ≫ (modelScalarCone S d).π.app (op i)) :
    ∃ (j : CoefficientStage S) (hij : i ≤ j), ∀ r : I,
      extendModelMorphism S (𝟙 (Spec (.of S))) (p r) hij (s r) ≫
        extendModelMorphism S (p r) d hij (c r) =
      extendModelMorphism S (𝟙 (Spec (.of S))) d hij (a r) := by
  have hfg : ∀ r : I,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (s r ≫ c r).left =
        (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op i) ≫ (a r).left :=
    fun r => triangle_comparison _ _ _ (sK r) (cK r) (aK r)
      (s r) (c r) (a r) (hs r) (hc r) (ha r) (he r)
  obtain ⟨j, hij, h⟩ := exists_stage_arrow_eqs S hS
    (fun _ : I => Spec (.of S)) (fun _ : I => D)
    (fun _ : I => 𝟙 _) (fun _ : I => d) i (fun r => s r ≫ c r) a hfg
  exact ⟨j, hij, fun r => (extended_comp S (𝟙 _) (p r) d hij (s r) (c r)).symm.trans (h r)⟩

end FrobeniusSplitting
