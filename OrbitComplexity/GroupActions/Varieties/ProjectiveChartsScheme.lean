import OrbitComplexity.GroupActions.Varieties.ProjectiveCharts
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsBasis
import OrbitComplexity.GroupActions.Varieties.AffineVariety

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
/-! # Standard affine charts of projective space

The homogeneous coordinate opens are spectra of polynomial rings in the remaining
coordinates. These opens form an affine cover over the coefficient ring. Over a field,
they prove reducedness and give the projective-space variety.

## Main definitions

* `GroupActions.projectiveChartIso`: the standard affine chart isomorphism.
* `GroupActions.projectiveChartCover`: the standard chart cover.
* `GroupActions.projectiveVariety`: projective space as a variety over a field.
-/

namespace GroupActions
variable (R ι : Type u) [CommRing R] [Finite ι]

omit [Finite ι] in
private theorem homogeneous_X (j : ι) : X j ∈ homogeneousSubmodule ι R 1 :=
  isHomogeneous_X R j

/-- A homogeneous coordinate open is affine space in its remaining coordinate ratios. -/
def projectiveChartIso (j : ι) :
    (Proj.basicOpen (homogeneousSubmodule ι R) (X j)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R)) :=
  Proj.basicOpenIsoSpec _ _ (homogeneous_X R ι j) Nat.zero_lt_one ≪≫
    Scheme.Spec.mapIso (projectiveChartRingEquiv R ι j).toCommRingCatIso.op

/-- The affine coordinate chart maps openly into projective space. -/
def projectiveChartMap (j : ι) :
    Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R)) ⟶ projectiveScheme R ι :=
  (projectiveChartIso R ι j).inv ≫ (Proj.basicOpen (homogeneousSubmodule ι R) (X j)).ι

private theorem chartMap_eq (j : ι) : projectiveChartMap R ι j =
    Spec.map (projectiveChartRingEquiv R ι j).toCommRingCatIso.inv ≫
      Proj.awayι _ _ (homogeneous_X R ι j) Nat.zero_lt_one := by
  simp only [projectiveChartMap, projectiveChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Category.assoc]
  rfl

/-- Standard affine chart morphisms are open immersions. -/
instance projectiveChartMap_isOpen (j : ι) : IsOpenImmersion (projectiveChartMap R ι j) := by
  unfold projectiveChartMap
  infer_instance

/-- The image of a standard chart is the distinguished homogeneous coordinate open. -/
theorem projectiveChartMap_range (j : ι) :
    (projectiveChartMap R ι j).opensRange = Proj.basicOpen (homogeneousSubmodule ι R) (X j) := by
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (Proj.basicOpen (homogeneousSubmodule ι R) (X j)).opensRange_ι

/-- A standard chart commutes with the structure morphism to the coefficient ring. -/
theorem projectiveChartMap_toSpec (j : ι) :
    projectiveChartMap R ι j ≫ projectiveToSpec R ι =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial {i : ι // i ≠ j} R)) := by
  have h : (projectiveChartRingEquiv R ι j).symm.toRingHom.comp
      ((fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (X j))).comp
        (projectiveZeroIso R ι).toRingHom) = C := by
    apply RingHom.ext
    intro r
    change (projectiveChartRingEquiv R ι j).symm
      (fromZeroRingHom _ _ (projectiveZeroIso R ι r)) = C r
    rw [← projectiveChartRingEquiv_C, RingEquiv.symm_apply_apply]
  rw [chartMap_eq, projectiveToSpec, Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

private theorem chart_covers (x : projectiveScheme R ι) :
    ∃ (j : ι) (y : Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R))),
      projectiveChartMap R ι j y = x := by
  have he := Proj.iSup_basicOpen_eq_top (homogeneousSubmodule ι R)
    (X : ι → MvPolynomial ι R) (projective_irrelevant_eq_span R ι).le
  have hx : x ∈ ⨆ j : ι, Proj.basicOpen (homogeneousSubmodule ι R) (X j) := by
    rw [he]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [← projectiveChartMap_range R ι j] at hj
  obtain ⟨y, hy⟩ := hj
  exact ⟨j, y, hy⟩

/-- The standard coordinate charts cover projective space. -/
def projectiveChartCover : Scheme.OpenCover (projectiveScheme R ι) where
  I₀ := ι
  X j := Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} R))
  f j := projectiveChartMap R ι j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨chart_covers R ι, inferInstance⟩

/-- Projective space over a field is reduced, as seen on its polynomial coordinate charts. -/
instance projectiveScheme_reduced (K ι : Type u) [Field K] [Finite ι] :
    IsReduced (projectiveScheme K ι) := by
  let : ∀ j : (projectiveChartCover K ι).I₀, IsReduced ((projectiveChartCover K ι).X j) :=
    fun j => inferInstanceAs (IsReduced (Spec (CommRingCat.of (MvPolynomial {i : ι // i ≠ j} K))))
  exact IsReduced.of_openCover _ (projectiveChartCover K ι)

/-- Projective space over a field is a reduced separated variety of finite type. -/
def projectiveVariety (K ι : Type u) [Field K] [Finite ι] : GroupActions.Variety K where
  scheme := projectiveScheme K ι
  toSpec := projectiveToSpec K ι

/-- The standard affine chart is a variety morphism over its field of coefficients. -/
def projectiveChartMorphism (K ι : Type u) [Field K] [Finite ι] (j : ι) :
    (affineVariety K (MvPolynomial {i : ι // i ≠ j} K)).toOver ⟶
      (projectiveVariety K ι).toOver :=
  Over.homMk (projectiveChartMap K ι j) (projectiveChartMap_toSpec K ι j)

/-- Standard affine variety charts of projective space are open immersions. -/
instance projectiveChartMorphism_isOpen (K ι : Type u) [Field K] [Finite ι] (j : ι) :
    IsOpenImmersion (projectiveChartMorphism K ι j).left := projectiveChartMap_isOpen K ι j

end GroupActions
