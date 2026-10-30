import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Batteries.Tactic.Lint

/-! # Coefficient change on polynomial charts of a projective line -/

open CategoryTheory AlgebraicGeometry GroupActions
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CoefficientCharts

private theorem polynomialChart_eq (R : Type u) [CommRing R]
    (j : ULift.{u} (Fin 2)) : projectiveLinePolynomialChart R j =
    Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
      {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
        projectiveChartMap R (ULift.{u} (Fin 2)) j := rfl

private theorem unique_map (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (σ : Type u) [Unique σ] :
    (MvPolynomial.uniqueAlgEquiv R σ).toRingHom.comp (MvPolynomial.map f) =
      (Polynomial.mapRingHom f).comp (MvPolynomial.uniqueAlgEquiv S σ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro s
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.C s)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.C s))
    simp only [MvPolynomial.map_C, MvPolynomial.eval₂_C, Polynomial.map_C]
  · intro i
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.X i)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.X i))
    simp only [MvPolynomial.map_X, MvPolynomial.eval₂_X, Polynomial.map_X]

/-- The coefficient morphism acts on a polynomial chart by coefficientwise polynomial mapping. -/
private theorem projectiveLinePolynomial_coeff (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        projectiveLinePolynomialChart S j := by
  have hc : CommRingCat.ofHom (MvPolynomial.map f) ≫
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom =
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom ≫
      CommRingCat.ofHom (Polynomial.mapRingHom f) := by
    apply CommRingCat.hom_ext
    exact unique_map S R f {i : ULift.{u} (Fin 2) // i ≠ j}
  have hs := congrArg (fun h => Spec.map h) hc
  simp only [Spec.map_comp] at hs
  rw [polynomialChart_eq, polynomialChart_eq, Category.assoc, projectiveCoeffMap_chart,
    ← Category.assoc, hs, Category.assoc]



end SchubertGeometry.CoefficientCharts
