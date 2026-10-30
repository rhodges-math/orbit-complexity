import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneSections

/-! # rank-one frames in the polynomial projective-line coordinates -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u

/-- The additive chart and polynomial chart use the same generator and chart index. -/
theorem projectiveChart_polynomial (K : Type u) [Field K] (j : ULift.{u} (Fin 2)) :
    (projectiveLineChart K j).left =
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
        projectiveLinePolynomialChart K j := by
  have h : Polynomial.aeval (SymmetricAlgebra.ι K K 1) =
      (gaPolynomialEquiv K).symm.toAlgHom := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    apply (gaPolynomialEquiv K).injective
    rw [gaPolynomialEquiv_generator]
    exact ((gaPolynomialEquiv K).apply_symm_apply Polynomial.X).symm
  have hc := projectiveLineChart_polynomial K j
  change (projectiveLineChart K j).left =
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) ≫
        projectiveLinePolynomialChart K j at hc
  rw [h] at hc
  exact hc

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The specified positive frame projects to polynomial chart zero with its specified parameter. -/
theorem simplePositiveSection_polynomial (i : G.rootBase.support) :
    (simplePositiveSection G i ≫ flagQuotientMorphism G).left =
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
        projectiveLinePolynomialChart K ⟨0⟩ ≫
          ((simpleSchubertIso G i).inv ≫
            schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
  rw [simplePositiveSection_chart]
  change (projectiveLineChart K ⟨0⟩).left ≫
    ((simpleSchubertIso G i).inv ≫
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left = _
  rw [projectiveChart_polynomial]
  exact Category.assoc _ _ _

/-- The specified negative frame projects to polynomial chart one with its specified parameter. -/
theorem simpleNegativeSection_polynomial (i : G.rootBase.support) :
    (simpleNegativeSection G i ≫ flagQuotientMorphism G).left =
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
        projectiveLinePolynomialChart K ⟨1⟩ ≫
          ((simpleSchubertIso G i).inv ≫
            schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left := by
  rw [simpleNegativeSection_chart]
  change (projectiveLineChart K ⟨1⟩).left ≫
    ((simpleSchubertIso G i).inv ≫
      schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left = _
  rw [projectiveChart_polynomial]
  exact Category.assoc _ _ _

end SchubertGeometry.ProjectiveLine
