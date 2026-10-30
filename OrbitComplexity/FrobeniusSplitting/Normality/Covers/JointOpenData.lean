import OrbitComplexity.FrobeniusSplitting.Normality.Models.ScalarImageDiagram
import OrbitComplexity.FrobeniusSplitting.Normality.PrincipalCovers
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageGraphs
import Mathlib.RingTheory.Smooth.Flat
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.ChosenOpenModels

/-! # Joint chosen open-model comparisons -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w z
namespace FrobeniusSplitting

/-- The same chosen models retain both principal denominators and prescribed finite values. -/
def jointOpenModelSpec {C : Type v} [Category.{w} C] {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (M : C ⥤ CommAlgCat.{u} S) (F : C ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i)
    (V : C → Type z) (values : ∀ i, V i → F.obj i) : Prop :=
  let arrows := Σ i : C, Σ j : C, i ⟶ j
  ∃ (L : arrows → Type u) (_ : ∀ b, Finite (L b)) (a : ∀ b, L b → F.obj b.1),
    (∀ b, Ideal.span (Set.range (fun j ↦ (F.map b.2.2).hom (a b j))) = ⊤) ∧
    (∀ b j, Function.Bijective (Localization.awayMap (F.map b.2.2).hom.toRingHom (a b j))) ∧
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      ∃ (P : ∀ i, Subalgebra T (F.obj i)) (eP : ∀ i, K ⊗[T] P i ≃ₐ[K] F.obj i)
        (d : ∀ {i j}, (i ⟶ j) → P i →ₐ[T] P j)
        (hd : ∀ i j (f : i ⟶ j) x, (d f x).val = (F.map f).hom x.val),
        T.FG ∧ (∀ i, Algebra.FinitePresentation T (P i)) ∧
        (∀ i, Algebra.Smooth T (P i)) ∧
        (∀ i (x : P i), eP i ((1 : K) ⊗ₜ[T] x) = x.val) ∧
        (∀ i v, values i v ∈ P i) ∧
        (∀ i, P i = (scalarImageHom (R := T) (e i)).range) ∧
        (∃ g : ∀ b, L b → P b.1,
          ∀ b j, eP b.1 ((1 : K) ⊗ₜ[T] g b j) = a b j) ∧
        let N := modelFunctor (fun i ↦ P i) (F ⋙ forget₂ (CommAlgCat K) CommRingCat)
          d (fun i ↦ (P i).val.toRingHom) (fun _ ↦ Subtype.val_injective) hd
        (∃ u : fixedFibreDiagram (R := T) (M := T) M ≅ N,
          ∀ i x, (P i).val ((u.hom.app i).hom x) = scalarImageHom (R := T) (e i) x) ∧
        chosenOpenModelSpec T N F eP

end FrobeniusSplitting
