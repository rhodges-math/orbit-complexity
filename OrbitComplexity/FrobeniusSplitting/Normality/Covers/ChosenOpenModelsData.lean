import OrbitComplexity.FrobeniusSplitting.Normality.Models.ScalarImageBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.OpenModelMaps
import Mathlib.RingTheory.Smooth.Flat

/-! # Specification of open models preserving the chosen coefficient diagram -/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- Open models retain the full prior coordinate diagram by coefficient base change. -/
def chosenOpenModelSpec {C : Type v} [Category.{w} C] {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (M : C ⥤ CommAlgCat.{u} S) (F : C ⥤ CommAlgCat.{u} K)
    (e : ∀ i, K ⊗[S] M.obj i ≃ₐ[K] F.obj i) : Prop :=
  ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    ∃ (N : C ⥤ CommAlgCat.{u} R) (eN : ∀ i, K ⊗[R] N.obj i ≃ₐ[K] F.obj i),
      R.FG ∧ (∀ i, Algebra.FinitePresentation R (N.obj i)) ∧
      (∀ i, Algebra.Smooth R (N.obj i)) ∧
      (∀ i j (f : i ⟶ j), (eN j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (eN i).toAlgHom) ∧
      (∀ i, Function.Injective (fun x : N.obj i ↦ eN i ((1 : K) ⊗ₜ[R] x))) ∧
      (∀ i j (f : i ⟶ j), IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))) ∧
      (∀ (i j k l : C) (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
        IsPushout (CommRingCat.ofHom (F.map f).hom.toRingHom)
          (CommRingCat.ofHom (F.map g).hom.toRingHom)
          (CommRingCat.ofHom (F.map p).hom.toRingHom)
          (CommRingCat.ofHom (F.map q).hom.toRingHom) →
        IsPushout (CommRingCat.ofHom (N.map f).hom.toRingHom)
          (CommRingCat.ofHom (N.map g).hom.toRingHom)
          (CommRingCat.ofHom (N.map p).hom.toRingHom)
          (CommRingCat.ofHom (N.map q).hom.toRingHom)) ∧
      ∃ q : fixedFibreDiagram (R := R) (M := R) M ≅ N,
        ∀ i z, eN i ((1 : K) ⊗ₜ[R] (q.hom.app i).hom z) =
          scalarImageHom (R := R) (e i) z

end FrobeniusSplitting
