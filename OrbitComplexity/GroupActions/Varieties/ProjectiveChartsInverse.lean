import OrbitComplexity.GroupActions.Varieties.ProjectiveCharts

/-! Dehomogenization in standard projective charts. -/

open MvPolynomial HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroupActions
variable (R ι : Type u) [CommRing R]

/-- Set the distinguished homogeneous coordinate to one. -/
def projectiveDehomogenize (j : ι) :
    MvPolynomial ι R →+* MvPolynomial {i : ι // i ≠ j} R := by
  classical
  exact eval₂Hom C (fun i => if h : i = j then 1 else X ⟨i, h⟩)

/-- A homogeneous fraction dehomogenizes by setting its denominator coordinate to one. -/
theorem projectiveChartRingEquiv_symm_mk [Finite ι] (j : ι) (n : ℕ)
    (p : MvPolynomial ι R) (hp : p ∈ homogeneousSubmodule ι R (n • 1)) :
    (projectiveChartRingEquiv R ι j).symm
        (Away.mk _ (isHomogeneous_X R j) n p hp) = projectiveDehomogenize R ι j p := by
  have h : projectiveDehomogenize R ι j (X j) = 1 := by
    classical
    simp [projectiveDehomogenize]
  let s : Submonoid.powers (X j : MvPolynomial ι R) := ⟨X j ^ n, ⟨n, rfl⟩⟩
  change IsLocalization.Away.lift (g := projectiveDehomogenize R ι j) (X j)
    (by rw [h]; exact isUnit_one) (Localization.mk p s) = _
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  change projectiveDehomogenize R ι j p =
    projectiveDehomogenize R ι j (X j ^ n) * projectiveDehomogenize R ι j p
  rw [map_pow, h, one_pow, one_mul]

end GroupActions
