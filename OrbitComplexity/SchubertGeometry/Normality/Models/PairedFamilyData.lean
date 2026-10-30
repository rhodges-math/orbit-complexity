import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyData
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedAffineSmooth

/-! # A common pointed model for finite paired-source coordinates

The specified affine opens supply smooth tensor coordinates from flag
transversality. The target keeps all chosen model nodes and arrows together.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions SchubertGeometry
open scoped TensorProduct
open FrobeniusSplitting

namespace SchubertGeometry.PointedFamilies
universe u v w

/-- A finite paired-source coordinate diagram has one common pointed
coefficient model on its specified flat presentation diagram. -/
def pairedFamily : Prop :=
  ∀ {J : Type v} [Category.{w} J] [Finite J]
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (S : Subalgebra ℤ K) (_ : S.FG)
    (P : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    [∀ i, Algebra.FinitePresentation S (P.obj i)] [∀ i, Module.Flat S (P.obj i)]
    (j : ∀ i, Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (F.obj i)))) ⟶
      pairedBSDHSource G a b) [∀ i, IsOpenImmersion (j i).left]
    (e : ∀ i, K ⊗[S] P.obj i ≃ₐ[K] F.obj i)
    (_ : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
        (F.map f).hom.comp (e i).toAlgHom),
    let B := G.borelAlgebra ⊗[K] G.oppositeBorelAlgebra
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
          (Bialgebra.counitAlgHom K B) (eH (k ⊗ₜ[R] h)) = k * algebraMap R K (eps0 h)) ∧
        (∀ i, (productModelEquiv (eR i) eH).toAlgHom.comp
            (Algebra.TensorProduct.map (AlgHom.id K K)
              ((Algebra.TensorProduct.includeLeft :
                N.obj i →ₐ[N.obj i] N.obj i ⊗[R] H0).restrictScalars R)) =
          (Algebra.TensorProduct.includeLeft :
            F.obj i →ₐ[K] F.obj i ⊗[K] B).comp (eR i).toAlgHom) ∧
        (∀ i, (eR i).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K K)
            (pointedProductRetraction (A := N.obj i) eps0)) =
          (pointedProductRetraction (A := F.obj i) (Bialgebra.counitAlgHom K B)).comp
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

end SchubertGeometry.PointedFamilies
