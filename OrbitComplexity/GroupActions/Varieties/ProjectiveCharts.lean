import OrbitComplexity.GroupActions.Varieties.ProjectiveSpace
import Mathlib.RingTheory.Localization.Away.Basic

open HomogeneousLocalization MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-! # Coordinate rings of projective-space charts

The degree-zero localization at a homogeneous variable is a polynomial ring in the
remaining coordinate ratios. Setting the distinguished variable to one constructs the
inverse map through ordinary localization.

## Main definitions

* `GroupActions.projectiveChartRingEquiv`: polynomial coordinates on a standard chart.

## Main results

* `GroupActions.projectiveChartRingEquiv_X`: variables map to homogeneous coordinate ratios.
* `GroupActions.projectiveChartRingEquiv_C`: coefficients retain their constant values.
-/

namespace GroupActions
variable (R ι : Type u) [CommRing R]

private abbrev ChartRing (j : ι) :=
  HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X j)

private def chartCoeff (j : ι) : R →+* ChartRing R ι j :=
  (fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (X j))).comp
    (projectiveZeroIso R ι).toRingHom

private def ratio (j i : ι) : ChartRing R ι j :=
  Away.isLocalizationElem (isHomogeneous_X R j) (isHomogeneous_X R i)

private theorem ratio_self (j : ι) : ratio R ι j j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one]
  exact Localization.mk_self (S := Submonoid.powers (X j : MvPolynomial ι R))
    ⟨X j ^ 1, ⟨1, rfl⟩⟩

private def homogenize (j : ι) : MvPolynomial {i : ι // i ≠ j} R →+* ChartRing R ι j :=
  eval₂Hom (chartCoeff R ι j) (fun i => ratio R ι j i.val)

private def dehomogenize (j : ι) : MvPolynomial ι R →+* MvPolynomial {i : ι // i ≠ j} R :=
  by
    classical
    exact eval₂Hom C (fun i => if h : i = j then 1 else X ⟨i, h⟩)

private theorem dehomogenize_self (j : ι) : dehomogenize R ι j (X j) = 1 := by
  classical
  simp [dehomogenize]

private def dehomogenizeAway (j : ι) :
    Localization.Away (X j : MvPolynomial ι R) →+* MvPolynomial {i : ι // i ≠ j} R :=
  IsLocalization.Away.lift (g := dehomogenize R ι j) (X j)
    (by rw [dehomogenize_self R ι j]; exact isUnit_one)

private def chartInverse (j : ι) : ChartRing R ι j →+* MvPolynomial {i : ι // i ≠ j} R :=
  (dehomogenizeAway R ι j).comp (algebraMap _ _)

private theorem inverse_mk (j : ι) (n : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ homogeneousSubmodule ι R (n • (1 : ℕ))) :
    chartInverse R ι j (Away.mk _ (isHomogeneous_X R j) n p hp) =
      dehomogenize R ι j p := by
  change dehomogenizeAway R ι j
    (Localization.mk p ⟨X j ^ n, by use n⟩) = _
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp [dehomogenize]

private theorem inverse_ratio (j : ι) (i : {i : ι // i ≠ j}) :
    chartInverse R ι j (ratio R ι j i.val) = X i := by
  classical
  change chartInverse R ι j (Away.mk _ (isHomogeneous_X R j) 1 _ _) = _
  rw [inverse_mk]
  simp [dehomogenize, i.property]

private theorem inverse_coeff (j : ι) (r : R) :
    chartInverse R ι j (chartCoeff R ι j r) = C r := by
  change dehomogenizeAway R ι j (Localization.mk (C r) 1) = _
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp [dehomogenize]

private theorem left_inverse (j : ι) :
    Function.LeftInverse (chartInverse R ι j) (homogenize R ι j) := by
  intro p
  have h : (chartInverse R ι j).comp (homogenize R ι j) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, homogenize, eval₂Hom_C, RingHom.id_apply] using
        inverse_coeff R ι j r
    · intro i
      simpa only [RingHom.comp_apply, homogenize, eval₂Hom_X', RingHom.id_apply] using
        inverse_ratio R ι j i
  exact DFunLike.congr_fun h p

private theorem ratios_mem_range (j i : ι) :
    ratio R ι j i ∈ (homogenize R ι j).range := by
  classical
  by_cases h : i = j
  · subst i
    rw [ratio_self]
    exact ⟨1, map_one _⟩
  · exact ⟨X ⟨i, h⟩, eval₂Hom_X' _ _ _⟩

private def rangeAlgebra (j : ι) :
    Subalgebra (homogeneousSubmodule ι R 0) (ChartRing R ι j) where
  __ := (homogenize R ι j).range.toSubsemiring
  algebraMap_mem' p := by
    refine ⟨C ((projectiveZeroIso R ι).symm p), ?_⟩
    rw [homogenize, eval₂Hom_C]
    change fromZeroRingHom (homogeneousSubmodule ι R) _
      ((projectiveZeroIso R ι) ((projectiveZeroIso R ι).symm p)) = _
    rw [RingEquiv.apply_symm_apply]
    rfl

private theorem fraction_prod [Fintype ι] (j : ι) (a : ℕ) (ai : ι → ℕ)
    (hp : (∏ i, X i ^ ai i : MvPolynomial ι R) ∈ homogeneousSubmodule ι R (a • 1))
    (h : ∑ i, ai i = a) :
    Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R j) a _ hp =
      ∏ i, ratio R ι j i ^ ai i := by
  apply (show Function.Injective
    (algebraMap (ChartRing R ι j) (Localization.Away (X j : MvPolynomial ι R))) from
      HomogeneousLocalization.val_injective _)
  simp only [map_prod, map_pow]
  change Localization.mk (∏ i, (X i : MvPolynomial ι R) ^ ai i) ⟨X j ^ a, by use a⟩ =
    ∏ i, Localization.mk (X i ^ 1) ⟨X j ^ 1, by use 1⟩ ^ ai i
  simp only [Localization.mk_pow, Localization.mk_prod]
  congr 1
  · simp only [← pow_mul, one_mul]
  · apply Subtype.ext
    simp only [SubmonoidClass.coe_pow,
      ← pow_mul, one_mul, Finset.prod_pow_eq_pow_sum, h]

private theorem homogenize_surjective [Finite ι] (j : ι) :
    Function.Surjective (homogenize R ι j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hgen : Algebra.adjoin (homogeneousSubmodule ι R 0)
      (Set.range (X : ι → MvPolynomial ι R)) = ⊤ := by
    apply eq_top_iff.mpr
    intro p hp_top
    clear hp_top
    induction p using MvPolynomial.induction_on with
    | C r => exact Subalgebra.algebraMap_mem _ (projectiveZeroIso R ι r)
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hspan := Away.span_mk_prod_pow_eq_top (isHomogeneous_X R j)
    (X : ι → MvPolynomial ι R) hgen (fun _ => 1) (fun i => isHomogeneous_X R i)
  have hr : (⊤ : Submodule (homogeneousSubmodule ι R 0) (ChartRing R ι j)) ≤
      (rangeAlgebra R ι j).toSubmodule := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ai, hai, rfl⟩
    rw [fraction_prod R ι j a ai _ (by simpa using hai)]
    exact Subalgebra.prod_mem _ (fun i _ =>
      Subalgebra.pow_mem _ (ratios_mem_range R ι j i) _)
  intro p
  exact hr (Submodule.mem_top : p ∈ (⊤ : Submodule _ _))

/-- A standard projective chart has the polynomial ring in its remaining coordinate ratios. -/
def projectiveChartRingEquiv [Finite ι] (j : ι) :
    MvPolynomial {i : ι // i ≠ j} R ≃+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X j) where
  __ := homogenize R ι j
  invFun := chartInverse R ι j
  left_inv := left_inverse R ι j
  right_inv := (left_inverse R ι j).rightInverse_of_surjective (homogenize_surjective R ι j)

/-- Each affine chart variable is the ratio to the distinguished homogeneous coordinate. -/
theorem projectiveChartRingEquiv_X [Finite ι] (j : ι) (i : {i : ι // i ≠ j}) :
    projectiveChartRingEquiv R ι j (X i) =
      Away.isLocalizationElem (isHomogeneous_X R j) (isHomogeneous_X R i.val) :=
  eval₂Hom_X' _ _ _

/-- Coefficients map to degree-zero constants in the homogeneous localization. -/
theorem projectiveChartRingEquiv_C [Finite ι] (j : ι) (r : R) :
    projectiveChartRingEquiv R ι j (C r) =
      fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (X j))
        (projectiveZeroIso R ι r) := eval₂Hom_C _ _ _

end GroupActions
