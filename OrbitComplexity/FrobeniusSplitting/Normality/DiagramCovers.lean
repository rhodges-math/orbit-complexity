import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PrincipalCovers
import OrbitComplexity.FrobeniusSplitting.Normality.DiagramElements

/-!
# Diagram Covers

Finite affine open diagrams admit models containing cover denominators.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

/-- Finite open diagrams admit arithmetic models containing finite principal-cover denominators. -/
theorem exists_open_diagram_elements {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (D : C ⥤ CommAlgCat.{u} K) [∀ i, Algebra.FinitePresentation K (D.obj i)]
    (hopen : ∀ i j (g : i ⟶ j),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map g).hom.toRingHom)))
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth K (D.obj i)) :
    let arrows := Σ i : C, Σ j : C, i ⟶ j
    ∃ (L : arrows → Type u) (_ : ∀ b, Finite (L b))
      (a : ∀ b, L b → D.obj b.1)
      (R : Subalgebra ℤ K) (D₀ : C ⥤ CommAlgCat.{u} R)
      (e : ∀ i, K ⊗[R] D₀.obj i ≃ₐ[K] D.obj i),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (D₀.obj i)) ∧
      (∀ i, i ∈ smoothNodes → Algebra.Smooth R (D₀.obj i)) ∧
      (∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
        (D.map f).hom.comp (e i).toAlgHom) ∧
      (∀ b, Ideal.span (Set.range (fun j ↦ (D.map b.2.2).hom (a b j))) = ⊤) ∧
      (∀ b j, Function.Bijective (Localization.awayMap (D.map b.2.2).hom.toRingHom (a b j))) ∧
      ∃ a₀ : ∀ b, L b → D₀.obj b.1,
        ∀ b j, e b.1 ((1 : K) ⊗ₜ[R] a₀ b j) = a b j := by
  classical
  let arrows := Σ i : C, Σ j : C, i ⟶ j
  choose L finiteL a hcover hlocal using fun b : arrows ↦
    (isOpenImmersion_iff_away_maps (D.map b.2.2).hom.toRingHom).mp
      (hopen b.1 b.2.1 b.2.2)
  let (b : arrows) : Finite (L b) := finiteL b
  let J (i : C) := Σ j : C, Σ g : i ⟶ j, L ⟨i, j, g⟩
  let elements (i : C) (j : J i) : D.obj i := a ⟨i, j.1, j.2.1⟩ j.2.2
  obtain ⟨R, D₀, e, hfg, hfp, hsmooth, hnatural, a₀, ha₀⟩ :=
    exists_arithmetic_diagram_elements D smoothNodes hsm J elements
  refine ⟨L, finiteL, a, R, D₀, e, hfg, hfp, hsmooth, hnatural, hcover, hlocal,
    (fun b j ↦ a₀ b.1 ⟨b.2.1, b.2.2, j⟩), ?_⟩
  intro b j
  exact ha₀ b.1 ⟨b.2.1, b.2.2, j⟩

end FrobeniusSplitting
