import OrbitComplexity.SchubertGeometry.ProjectiveLine.RootParameters
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts

/-! # Polynomial coordinates of the additive projective charts -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
variable (K : Type u) [Field K]

private def gaPolynomialMap : Polynomial K →ₐ[K] SymmetricAlgebra K K :=
  Polynomial.aeval (SymmetricAlgebra.ι K K 1)

private theorem coordinateFactor (σ : Type u) [Unique σ] :
    (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton σ K)).symm.toAlgHom =
      (gaPolynomialMap K).comp (MvPolynomial.uniqueAlgEquiv K σ).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton σ K)).symm
      (MvPolynomial.X i) =
    gaPolynomialMap K (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (MvPolynomial.X i))
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X, Module.Basis.singleton_apply,
    MvPolynomial.eval₂_X]
  simp only [gaPolynomialMap, Polynomial.aeval_X]

private theorem polynomialChart_eq (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart K j =
      Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv K
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          projectiveChartMap K (ULift.{u} (Fin 2)) j := rfl

/-- The additive projective chart uses the polynomial coordinate determined by its tangent. -/
theorem projectiveLineChart_polynomial (j : ULift.{u} (Fin 2)) :
    (projectiveLineChart K j).left =
      Spec.map (CommRingCat.ofHom (gaPolynomialMap K).toRingHom) ≫
        projectiveLinePolynomialChart K j := by
  have hc : CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv K
      {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom ≫
      CommRingCat.ofHom (gaPolynomialMap K).toRingHom =
    CommRingCat.ofHom
      (SymmetricAlgebra.equivMvPolynomial
        (Module.Basis.singleton {i : ULift.{u} (Fin 2) // i ≠ j} K)).symm.toRingHom := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (coordinateFactor K
      {i : ULift.{u} (Fin 2) // i ≠ j}).symm
  rw [polynomialChart_eq, ← Category.assoc, ← Spec.map_comp, hc]
  rfl

end SchubertGeometry
