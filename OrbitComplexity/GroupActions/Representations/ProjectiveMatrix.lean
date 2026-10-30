import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsBasis
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Matrix morphisms of projective space

An invertible matrix gives a homogeneous polynomial substitution and hence a morphism
of projective schemes. The morphism is compatible with the coefficient structure maps.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped Matrix
universe u v w

section Structure
variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem away_map_zero (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    (Away.map f s).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (f s))).comp f.gradedZeroRingHom := by
  apply RingHom.ext
  intro x
  let hle : Submonoid.powers s ≤ (Submonoid.powers (f s)).comap f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  change HomogeneousLocalization.map f hle (HomogeneousLocalization.mk ⟨0, x, 1, _⟩) =
    HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom x, 1, _⟩
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (f x.val) ⟨f (1 : A), by rw [map_one]; exact one_mem _⟩ =
    Localization.mk (f x.val) 1
  congr 1
  exact Subtype.ext (map_one f)

private theorem graded_map_base (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (Σ i : PNat, 𝒜 i) at s
  rcases s with ⟨⟨n, hn⟩, s, hs⟩
  change s ∈ 𝒜 n at hs
  change Proj.awayι ℬ (f s) (f.map_mem hs) hn ≫
      (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f s) (f.map_mem hs) hn ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  rw [← Category.assoc, Proj.awayι_comp_map f hf hn s hs, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (away_map_zero f s)

end Structure

section Matrix
variable {K : Type u} {H : Type v} {ι : Type w}
  [CommRing K] [CommRing H] [Algebra K H] [Fintype ι]
attribute [local instance] MvPolynomial.gradedAlgebra

private def coordinateImage (a : Matrix ι ι H) (i : ι) : MvPolynomial ι H :=
  ∑ j, C (a i j) * X j

private theorem coordinateImage_homogeneous (a : Matrix ι ι H) (i : ι) :
    (coordinateImage a i).IsHomogeneous 1 := by
  change (∑ j, C (a i j) * X j) ∈ homogeneousSubmodule ι H 1
  apply Submodule.sum_mem
  intro j hj
  simpa only [mem_homogeneousSubmodule, zero_add] using
    (isHomogeneous_C ι (a i j)).mul (isHomogeneous_X H j)

/-- Linear substitution by a matrix preserves the polynomial grading. -/
def projectiveMatrixHom (a : Matrix ι ι H) :
    homogeneousSubmodule ι K →+*ᵍ homogeneousSubmodule ι H where
  __ := (aeval (coordinateImage a) : MvPolynomial ι K →ₐ[K] MvPolynomial ι H).toRingHom
  map_mem {i} {p} hp := by
    change (aeval (coordinateImage a) p).IsHomogeneous i
    simpa only [one_mul] using hp.aeval (coordinateImage a) (coordinateImage_homogeneous a)

/-- A homogeneous coordinate pulls back to the corresponding matrix row. -/
theorem projectiveMatrixHom_X (a : Matrix ι ι H) (i : ι) :
    projectiveMatrixHom (K := K) a (X i) = ∑ j, C (a i j) * X j :=
  aeval_X (coordinateImage a) i

/-- Matrix substitution extends the coefficient algebra map. -/
theorem projectiveMatrixHom_C (a : Matrix ι ι H) (r : K) :
    projectiveMatrixHom (K := K) a (C r) = C (algebraMap K H r) := by
  change aeval (coordinateImage a) (C r) = _
  rw [aeval_C]
  rfl

variable [DecidableEq ι]

private theorem inverse_coordinates (a : Matrix.GeneralLinearGroup ι H) (i : ι) :
    (∑ j, C ((a⁻¹ : Matrix.GeneralLinearGroup ι H) i j) *
      projectiveMatrixHom (K := K) (a : Matrix ι ι H) (X j)) = X i := by
  simp only [projectiveMatrixHom_X]
  change (a.inv.map (C : H →+* MvPolynomial ι H) *ᵥ
    ((a : Matrix ι ι H).map (C : H →+* MvPolynomial ι H) *ᵥ X)) i = X i
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, a.inv_val]
  rw [Matrix.map_one C (map_zero _) (map_one _), Matrix.one_mulVec]

private theorem matrix_irrelevant {R A idx : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Fintype idx] [DecidableEq idx] (a : Matrix.GeneralLinearGroup idx A) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule idx A) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule idx R)).map
        (projectiveMatrixHom (a : Matrix idx idx A)) := by
  rw [← toIdeal_le_toIdeal_iff,
    GroupActions.projective_irrelevant_eq_span, HomogeneousIdeal.toIdeal_map]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← inverse_coordinates (K := R) a i]
  apply Ideal.sum_mem
  intro j hj
  apply Ideal.mul_mem_left
  apply Ideal.mem_map_of_mem
  rw [GroupActions.projective_irrelevant_eq_span]
  exact Ideal.subset_span ⟨j, rfl⟩

/-- An invertible coefficient matrix induces a morphism of projective schemes. -/
def projectiveMatrixMap {R A idx : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Fintype idx] [DecidableEq idx] (a : Matrix.GeneralLinearGroup idx A) :
    GroupActions.projectiveScheme A idx ⟶ GroupActions.projectiveScheme R idx :=
  Proj.map (projectiveMatrixHom (a : Matrix idx idx A)) (matrix_irrelevant a)

/-- The homogeneous prime of a matrix image is the substitution preimage. -/
theorem projectiveMatrixMap_mem {R A idx : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Fintype idx] [DecidableEq idx] (a : Matrix.GeneralLinearGroup idx A)
    (x : GroupActions.projectiveScheme A idx) (p : MvPolynomial idx R) :
    p ∈ (projectiveMatrixMap a x).asHomogeneousIdeal ↔
      projectiveMatrixHom (a : Matrix idx idx A) p ∈ x.asHomogeneousIdeal := Iff.rfl

/-- The projective matrix morphism commutes with the coefficient structure maps. -/
theorem projectiveMatrixMap_toSpec {R A idx : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Fintype idx] [DecidableEq idx] (a : Matrix.GeneralLinearGroup idx A) :
    projectiveMatrixMap a ≫ GroupActions.projectiveToSpec R idx =
      GroupActions.projectiveToSpec A idx ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  have he : (GroupActions.projectiveZeroIso R idx).toCommRingCatIso.hom ≫
      CommRingCat.ofHom (projectiveMatrixHom (a : Matrix idx idx A)).gradedZeroRingHom =
      CommRingCat.ofHom (algebraMap R A) ≫
        (GroupActions.projectiveZeroIso A idx).toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply Subtype.ext
    change projectiveMatrixHom (a : Matrix idx idx A) (C r) = C (algebraMap R A r)
    exact projectiveMatrixHom_C (a : Matrix idx idx A) r
  change Proj.map (projectiveMatrixHom (a : Matrix idx idx A)) (matrix_irrelevant a) ≫
      (Proj.toSpecZero (homogeneousSubmodule idx R) ≫
        Spec.map (GroupActions.projectiveZeroIso R idx).toCommRingCatIso.hom) =
    (Proj.toSpecZero (homogeneousSubmodule idx A) ≫
      Spec.map (GroupActions.projectiveZeroIso A idx).toCommRingCatIso.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← CategoryTheory.Category.assoc, graded_map_base,
    CategoryTheory.Category.assoc, ← Spec.map_comp, CategoryTheory.Category.assoc,
    ← Spec.map_comp, he]
end Matrix

end GroupActions
