import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of polynomial projective space

The standard affine charts are finite polynomial schemes over the coefficient ring.
Smoothness descends from this source cover.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u

namespace GroupActions

/-- Finite-coordinate projective space is smooth over its coefficient ring. -/
instance projectiveToSpec_smooth (R ι : Type u) [CommRing R] [Finite ι] :
    Smooth (projectiveToSpec R ι) := by
  let : ∀ j : (projectiveChartCover R ι).I₀,
      IsAffine ((projectiveChartCover R ι).X j) := fun j => by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R)))
    infer_instance
  apply HasRingHomProperty.of_source_openCover (P := @Smooth.{u})
    (projectiveChartCover R ι)
  intro j
  change ι at j
  have hs : Smooth ((projectiveChartCover R ι).f j ≫ projectiveToSpec R ι) := by
    change Smooth (projectiveChartMap R ι j ≫ projectiveToSpec R ι)
    rw [projectiveChartMap_toSpec]
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have : IsAffine ((projectiveChartCover R ι).X j) := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R)))
    infer_instance
  exact HasRingHomProperty.appTop (@Smooth.{u}) _ hs

end GroupActions
