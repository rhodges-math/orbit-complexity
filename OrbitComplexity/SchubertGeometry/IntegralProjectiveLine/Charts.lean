import Mathlib.Algebra.Polynomial.Laurent
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsOverlap
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsReciprocal
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Polynomial and Laurent charts of the projective line -/

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory Opposite GroupActions
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra


private theorem remainingUniqueExists (j : (ULift.{u} (Fin 2))) :
    Nonempty (Unique {i : (ULift.{u} (Fin 2)) // i ≠ j}) := by
  rcases j with ⟨j⟩
  fin_cases j
  · refine ⟨{ default := ⟨⟨1⟩, by decide⟩, uniq := ?_ }⟩
    rintro ⟨⟨i⟩, hi⟩
    apply Subtype.ext
    apply ULift.ext
    fin_cases i <;> first | rfl | exact False.elim (hi rfl)
  · refine ⟨{ default := ⟨⟨0⟩, by decide⟩, uniq := ?_ }⟩
    rintro ⟨⟨i⟩, hi⟩
    apply Subtype.ext
    apply ULift.ext
    fin_cases i <;> first | rfl | exact False.elim (hi rfl)

private instance remainingUnique (j : (ULift.{u} (Fin 2))) :
    Unique {i : (ULift.{u} (Fin 2)) // i ≠ j} := Classical.choice (remainingUniqueExists j)

variable (R : Type u) [CommRing R]

private abbrev chartOpen (j : (ULift.{u} (Fin 2))) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R) (MvPolynomial.X j)

/-- A homogeneous-coordinate chart of the projective line is the polynomial affine line. -/
def projectiveLinePolynomialIso (j : (ULift.{u} (Fin 2))) :
    Spec (.of (Polynomial R)) ≅
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
        (MvPolynomial.X j)).toScheme :=
  Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv R
    {i : (ULift.{u} (Fin 2)) // i ≠ j}).toRingEquiv.toCommRingCatIso.op ≪≫
      (projectiveChartIso R (ULift.{u} (Fin 2)) j).symm

/-- A standard projective-line chart parametrized by the polynomial coordinate. -/
def projectiveLinePolynomialChart (j : (ULift.{u} (Fin 2))) :
    Spec (.of (Polynomial R)) ⟶ projectiveScheme R (ULift.{u} (Fin 2)) :=
  (projectiveLinePolynomialIso R j).hom ≫ (chartOpen R j).ι

private theorem polynomialChart_eq (j : (ULift.{u} (Fin 2))) : projectiveLinePolynomialChart R j =
    Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
      {i : (ULift.{u} (Fin 2)) // i ≠ j}).toRingHom) ≫
        projectiveChartMap R (ULift.{u} (Fin 2)) j := rfl

/-- The polynomial chart is an open immersion. -/
instance projectiveLinePolynomialChart_open (j : (ULift.{u} (Fin 2))) :
    IsOpenImmersion (projectiveLinePolynomialChart R j) := by
  unfold projectiveLinePolynomialChart
  infer_instance

/-- The polynomial chart has the prescribed homogeneous-coordinate image. -/
theorem projectiveLinePolynomialChart_range (j : (ULift.{u} (Fin 2))) :
    (projectiveLinePolynomialChart R j).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
        (MvPolynomial.X j) := by
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chartOpen R j).opensRange_ι

/-- The other chart pulls back to the nonzero polynomial coordinate locus. -/
theorem projectiveLinePolynomial_preimage (j k : (ULift.{u} (Fin 2))) (hkj : k ≠ j) :
    projectiveLinePolynomialChart R j ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
        (MvPolynomial.X k) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  rw [polynomialChart_eq, Scheme.Hom.comp_preimage,
    projectiveChartMap_preimage R (ULift.{u} (Fin 2)) j ⟨k, hkj⟩]
  change PrimeSpectrum.basicOpen ((MvPolynomial.uniqueAlgEquiv R
    {i : (ULift.{u} (Fin 2)) // i ≠ j}) (MvPolynomial.X ⟨k, hkj⟩)) = _
  simp

/-- The polynomial chart commutes with the coefficient structure morphism. -/
theorem projectiveLinePolynomialChart_base (j : (ULift.{u} (Fin 2))) :
    projectiveLinePolynomialChart R j ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  rw [polynomialChart_eq, Category.assoc, projectiveChartMap_toSpec, ← Spec.map_comp]
  congr 1
  ext r
  simp

private def laurentInclusion : Spec (.of (LaurentPolynomial R)) ⟶
    Spec (.of (Polynomial R)) := Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

private instance laurentSpec_isOpen :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R))) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)

private instance laurentInclusion_isOpen : IsOpenImmersion (laurentInclusion R) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)

private theorem laurentInclusion_range : (laurentInclusion R).opensRange =
    PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  apply SetLike.coe_injective
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R) Polynomial.X

private theorem overlap_lifts :
    Set.range (laurentInclusion R ≫ projectiveLinePolynomialChart R ⟨0⟩) ⊆
    Set.range (projectiveLinePolynomialChart R ⟨1⟩) := by
  rintro _ ⟨x, rfl⟩
  change laurentInclusion R x ∈ projectiveLinePolynomialChart R ⟨0⟩ ⁻¹ᵁ
    (projectiveLinePolynomialChart R ⟨1⟩).opensRange
  rw [projectiveLinePolynomialChart_range, projectiveLinePolynomial_preimage R ⟨0⟩ ⟨1⟩ (by decide),
    ← laurentInclusion_range R]
  exact ⟨x, rfl⟩

private def reciprocalLift : Spec (.of (LaurentPolynomial R)) ⟶
    Spec (.of (Polynomial R)) :=
  IsOpenImmersion.lift (projectiveLinePolynomialChart R ⟨1⟩)
    (laurentInclusion R ≫ projectiveLinePolynomialChart R ⟨0⟩) (overlap_lifts R)

private theorem reciprocalLift_fac : reciprocalLift R ≫ projectiveLinePolynomialChart R ⟨1⟩ =
    laurentInclusion R ≫ projectiveLinePolynomialChart R ⟨0⟩ :=
  IsOpenImmersion.lift_fac _ _ _

private theorem reciprocalLift_C (r : R) :
    (Spec.preimage (reciprocalLift R)).hom (Polynomial.C r) = LaurentPolynomial.C r := by
  have h : reciprocalLift R ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)) := by
    rw [← projectiveLinePolynomialChart_base R ⟨1⟩, ← Category.assoc, reciprocalLift_fac,
      Category.assoc, projectiveLinePolynomialChart_base, laurentInclusion, ← Spec.map_comp]
    congr 1
    ext x
    simp
  have hr := congrArg (fun f => (Spec.preimage f).hom r) h
  simpa only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp,
    RingHom.comp_apply, CommRingCat.hom_ofHom] using hr

private theorem reciprocalLift_X :
    (Spec.preimage (reciprocalLift R)).hom Polynomial.X = LaurentPolynomial.T (-1) := by
  let e₀ := (MvPolynomial.uniqueAlgEquiv R {i : (ULift.{u} (Fin 2)) // i ≠ ⟨0⟩}).toRingHom
  let e₁ := (MvPolynomial.uniqueAlgEquiv R {i : (ULift.{u} (Fin 2)) // i ≠ ⟨1⟩}).toRingHom
  let a := laurentInclusion R ≫ Spec.map (CommRingCat.ofHom e₀)
  let b := reciprocalLift R ≫ Spec.map (CommRingCat.ofHom e₁)
  have hab : a ≫ projectiveChartMap R (ULift.{u} (Fin 2)) ⟨0⟩ =
      b ≫ projectiveChartMap R (ULift.{u} (Fin 2)) ⟨1⟩ := by
    change (laurentInclusion R ≫ Spec.map (CommRingCat.ofHom e₀)) ≫ _ =
      (reciprocalLift R ≫ Spec.map (CommRingCat.ofHom e₁)) ≫ _
    rw [Category.assoc, Category.assoc]
    exact (reciprocalLift_fac R).symm
  have h := projectiveChart_reciprocal R (ULift.{u} (Fin 2)) (LaurentPolynomial R)
    ⟨0⟩ ⟨1⟩ (by decide) a b hab
  have he₀ : e₀ (MvPolynomial.X ⟨⟨1⟩, by decide⟩) = Polynomial.X := by simp [e₀]
  have he₁ : e₁ (MvPolynomial.X ⟨⟨0⟩, by decide⟩) = Polynomial.X := by simp [e₁]
  change (Spec.preimage a).hom _ * (Spec.preimage b).hom _ = 1 at h
  dsimp only [a, b] at h
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h
  change (Spec.preimage (laurentInclusion R)).hom (e₀ _) *
    (Spec.preimage (reciprocalLift R)).hom (e₁ _) = 1 at h
  rw [he₀, he₁] at h
  rw [laurentInclusion, Spec.preimage_map, CommRingCat.hom_ofHom,
    Polynomial.toLaurent_X] at h
  calc
    (Spec.preimage (reciprocalLift R)).hom Polynomial.X =
        (Spec.preimage (reciprocalLift R)).hom Polynomial.X *
          (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by
      rw [← LaurentPolynomial.T_add]
      simp
    _ = (LaurentPolynomial.T 1 *
        (Spec.preimage (reciprocalLift R)).hom Polynomial.X) *
          LaurentPolynomial.T (-1) := by ring
    _ = LaurentPolynomial.T (-1) := by rw [h, one_mul]

private theorem reciprocalLift_eq : reciprocalLift R =
    Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
        Polynomial.toLaurent)) := by
  apply Spec.preimage_injective
  rw [Spec.preimage_map]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    exact (reciprocalLift_C R r).trans (by simp)
  · exact (reciprocalLift_X R).trans (by simp)

/-- The two polynomial charts agree after reciprocal Laurent-coordinate substitution. -/
theorem projectiveLinePolynomial_overlap :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent :
      Polynomial R →+* LaurentPolynomial R)) ≫ projectiveLinePolynomialChart R ⟨0⟩ =
        Spec.map (CommRingCat.ofHom
          ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
            Polynomial.toLaurent)) ≫ projectiveLinePolynomialChart R ⟨1⟩ := by
  rw [← reciprocalLift_eq]
  exact (reciprocalLift_fac R).symm

/-- The Laurent coordinate maps onto the intersection of the two polynomial charts. -/
theorem projectiveLinePolynomial_inter :
    (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent :
      Polynomial R →+* LaurentPolynomial R)) ≫ projectiveLinePolynomialChart R ⟨0⟩).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
        (MvPolynomial.X (⟨0⟩ : ULift.{u} (Fin 2))) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R)
        (MvPolynomial.X (⟨1⟩ : ULift.{u} (Fin 2))) := by
  change (laurentInclusion R ≫ projectiveLinePolynomialChart R ⟨0⟩).opensRange = _
  rw [Scheme.Hom.opensRange_comp, laurentInclusion_range,
    ← projectiveLinePolynomial_preimage R ⟨0⟩ ⟨1⟩ (by decide),
    Scheme.Hom.image_preimage_eq_opensRange_inf, projectiveLinePolynomialChart_range]

end
end SchubertGeometry
