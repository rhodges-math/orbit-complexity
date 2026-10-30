import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
/-! # Intersections of standard projective charts

Inside one standard affine chart, another homogeneous coordinate open is the basic open
where the corresponding coordinate ratio is invertible.
-/

namespace GroupActions
variable (R ι : Type u) [CommRing R] [Finite ι]

omit [Finite ι] in
private theorem homogeneous_X (j : ι) : X j ∈ homogeneousSubmodule ι R 1 :=
  isHomogeneous_X R j

private theorem chartMap_eq (j : ι) : projectiveChartMap R ι j =
    Spec.map (projectiveChartRingEquiv R ι j).toCommRingCatIso.inv ≫
      Proj.awayι _ _ (homogeneous_X R ι j) Nat.zero_lt_one := by
  simp only [projectiveChartMap, projectiveChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Category.assoc]
  rfl

/-- A second homogeneous coordinate chart restricts to the matching affine basic open. -/
theorem projectiveChartMap_preimage (j : ι) (i : {i : ι // i ≠ j}) :
    projectiveChartMap R ι j ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (X i.val) =
      PrimeSpectrum.basicOpen (X i : MvPolynomial {i : ι // i ≠ j} R) := by
  rw [chartMap_eq, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (homogeneous_X R ι j) Nat.zero_lt_one
      (homogeneous_X R ι i.val) Nat.zero_lt_one]
  change PrimeSpectrum.basicOpen ((projectiveChartRingEquiv R ι j).symm
    (Away.isLocalizationElem (homogeneous_X R ι j) (homogeneous_X R ι i.val))) = _
  rw [← projectiveChartRingEquiv_X, RingEquiv.symm_apply_apply]

end GroupActions
