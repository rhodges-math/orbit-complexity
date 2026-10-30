import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial subcharts of the scalar projective nodes

The existing polynomial atlas and the constructed projective nodes have the
same two projections. Their equality therefore follows in the prescribed
scalar model, for both polynomial charts.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions Polynomial
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private coefficient nodeBase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
open private projectiveLinePolynomial_coeff from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private theorem polynomialScalar_base {T A : Type u} [CommRing T] [CommRing A]
    [Algebra T A] (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart A j ≫ projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T A)) =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial A))) := by
  rw [← Category.assoc, projectiveLinePolynomialChart_base, ← Spec.map_comp]
  congr 1

/-- Each constructed projective node has precisely the polynomial chart map
of the existing scalar atlas, determined by its two retained projections. -/
theorem scalarProjective_polynomial_chart {S T A : Type u}
    [CommRing S] [CommRing T] [CommRing A] [Algebra S T] [Algebra S A]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (q : Y ⟶ X)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (old : line A ⟶ X) (K : line (T ⊗[S] A) ⟶ Y)
    (hOld : K ≫ q = coefficient S T A ≫ old)
    (hBase : K ≫ baseT = nodeBase S T A)
    (j : ULift.{u} (Fin 2))
    (k : Spec (.of (Polynomial (T ⊗[S] A))) ⟶ Y)
    (hkOld : k ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom)) ≫
        projectiveLinePolynomialChart A j ≫ old)
    (hkBase : k ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A))))) :
    projectiveLinePolynomialChart (T ⊗[S] A) j ≫ K = k := by
  apply hq.hom_ext
  · calc
      _ = projectiveLinePolynomialChart (T ⊗[S] A) j ≫ (K ≫ q) := Category.assoc _ _ _
      _ = (projectiveLinePolynomialChart (T ⊗[S] A) j ≫ coefficient S T A) ≫ old := by
        rw [hOld, Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom)) ≫
            projectiveLinePolynomialChart A j) ≫ old :=
        congrArg (fun f => f ≫ old) (projectiveLinePolynomial_coeff A (T ⊗[S] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom j)
      _ = _ := hkOld.symm
  · calc
      _ = projectiveLinePolynomialChart (T ⊗[S] A) j ≫ (K ≫ baseT) := Category.assoc _ _ _
      _ = projectiveLinePolynomialChart (T ⊗[S] A) j ≫ nodeBase S T A :=
        congrArg (fun f => projectiveLinePolynomialChart (T ⊗[S] A) j ≫ f) hBase
      _ = Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A)))) :=
        polynomialScalar_base j
      _ = _ := hkBase.symm

end SchubertGeometry.RetainedCharacter
