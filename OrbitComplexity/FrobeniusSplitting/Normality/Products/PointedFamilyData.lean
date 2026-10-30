import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedSourceModels
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams

/-! # A specified finite diagram with one pointed product factor

This is an independent target for a coefficient-model producer, not a premise
available to any normality theorem.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FrobeniusSplitting.PointedFamilies
universe u v w

/-- One coefficient extension retains a specified finite node-and-arrow diagram
and one shared smooth auxiliary factor and counit. -/
def pointedFamily : Prop :=
  ∀ {J : Type v} [Category.{w} J] [Finite J]
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    (S : Subalgebra ℤ K) (_ : S.FG)
    (P : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    [∀ i, Algebra.FinitePresentation S (P.obj i)] [∀ i, Module.Flat S (P.obj i)]
    [Algebra.Smooth K B] [∀ i, Algebra.Smooth K (F.obj i ⊗[K] B)]
    (e : ∀ i, K ⊗[S] P.obj i ≃ₐ[K] F.obj i)
    (_ : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
        (F.map f).hom.comp (e i).toAlgHom)
    (eps : B →ₐ[K] K),
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) P
      let eR (i : J) : K ⊗[R] N.obj i ≃ₐ[K] F.obj i :=
        (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj i)).trans (e i)
      ∃ (H0 : Type u) (_ : CommRing H0) (_ : Algebra R H0)
        (eH : K ⊗[R] H0 ≃ₐ[K] B) (eps0 : H0 →ₐ[R] R),
        R.FG ∧ Algebra.Smooth R H0 ∧
        (∀ i, Algebra.Smooth R (N.obj i)) ∧
        (∀ i, Algebra.Smooth R (N.obj i ⊗[R] H0)) ∧
        (∀ i, (pointedProductRetraction (A := N.obj i) eps0).comp
            ((Algebra.TensorProduct.includeLeft :
              N.obj i →ₐ[N.obj i] N.obj i ⊗[R] H0).restrictScalars R) =
          AlgHom.id R (N.obj i)) ∧
        (∀ i j (f : i ⟶ j), (eR j).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
            (F.map f).hom.comp (eR i).toAlgHom) ∧
        (∀ (k : K) (h : H0),
          eps (eH (k ⊗ₜ[R] h)) = k * algebraMap R K (eps0 h)) ∧
        (∀ i, (productModelEquiv (eR i) eH).toAlgHom.comp
            (Algebra.TensorProduct.map (AlgHom.id K K)
              ((Algebra.TensorProduct.includeLeft :
                N.obj i →ₐ[N.obj i] N.obj i ⊗[R] H0).restrictScalars R)) =
          (Algebra.TensorProduct.includeLeft :
            F.obj i →ₐ[K] F.obj i ⊗[K] B).comp (eR i).toAlgHom) ∧
        (∀ i, (eR i).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K K)
            (pointedProductRetraction (A := N.obj i) eps0)) =
          (pointedProductRetraction (A := F.obj i) eps).comp
            (productModelEquiv (eR i) eH).toAlgHom) ∧
        (∀ i j (f : i ⟶ j), (pointedProductRetraction (A := N.obj j) eps0).comp
            (Algebra.TensorProduct.map (N.map f).hom (AlgHom.id R H0)) =
          (N.map f).hom.comp (pointedProductRetraction (A := N.obj i) eps0)) ∧
        ∀ i (L : Type u) (_ : Field L) (f : R →+* L),
          ∀ z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R (N.obj i))))
              (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}),
            IsDomain ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R (N.obj i))))
              (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}).presheaf.stalk z) ∧
            IsIntegrallyClosed ((pullback
              (Spec.map (CommRingCat.ofHom (algebraMap R (N.obj i))))
              (Spec.map (CommRingCat.ofHom f)) : Scheme.{u}).presheaf.stalk z)

end FrobeniusSplitting.PointedFamilies
