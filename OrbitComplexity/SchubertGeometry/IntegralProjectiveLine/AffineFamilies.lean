import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import Mathlib.Tactic.CategoryTheory.Reassoc

/-! # Coefficient change on polynomial charts of a projective line -/

open CategoryTheory AlgebraicGeometry GroupActions
namespace SchubertGeometry

universe u

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

end SchubertGeometry

/-! # Affine projective transformations with varying coefficients -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
universe u
variable {K R : Type u} [CommRing K] [CommRing R]

private theorem coefficient_base (f : K →+* R) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ projectiveToSpec K (ULift.{u} (Fin 2)) =
      projectiveToSpec R (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← projectiveBaseChange_snd (ULift.{u} (Fin 2)) f, Category.assoc,
    ← Limits.pullback.condition, ← Category.assoc, projectiveBaseChange_fst]

/-- Scaling and translation over the coefficient ring give a regular projective-line family. -/
def projectiveAffineFamily (f : K →+* R) (c : Rˣ) (a : R) :
    (Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗
      Over.mk (projectiveToSpec K (ULift.{u} (Fin 2)))) ⟶
        Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))) :=
  Over.homMk ((projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
    (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) f) (by
    change ((projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f) ≫
          projectiveToSpec K (ULift.{u} (Fin 2)) =
      Limits.pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom f)
    have ht := congrArg (fun m => m ≫ Spec.map (CommRingCat.ofHom f))
      (projectiveLineTranslation_base a)
    have hs := congrArg (fun m => m ≫ Spec.map (CommRingCat.ofHom f))
      (projectiveLineScaling_base c)
    simp only [Category.assoc] at ht hs
    simp only [Category.assoc, coefficient_base, ht, hs]
    rw [← Category.assoc]
    congr 1
    apply (Iso.inv_comp_eq _).mpr
    exact (projectiveBaseChange_fst (ULift.{u} (Fin 2)) f).symm)

private theorem affine_polynomial (c : Rˣ) (a : R) :
    (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom.comp
      (Polynomial.algEquivAevalXAddC a).toRingHom =
        (Polynomial.algEquivCMulXAddC (c : R) a).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- The affine projective family sends the polynomial coordinate to cX plus a. -/
theorem projectiveAffineFamily_chart (f : K →+* R) (c : Rˣ) (a : R) :
    projectiveLinePolynomialChart R ⟨0⟩ ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
        (projectiveAffineFamily f c a).left =
      Spec.map (CommRingCat.ofHom
        ((Polynomial.algEquivCMulXAddC (c : R) a).toRingHom.comp
          (Polynomial.mapRingHom f))) ≫ projectiveLinePolynomialChart K ⟨0⟩ := by
  change projectiveLinePolynomialChart R ⟨0⟩ ≫
      (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
      (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f = _
  rw [Iso.hom_inv_id_assoc, ← reassoc_of% (projectiveLineScaling_chart c),
    ← reassoc_of% (projectiveLineTranslation_chart a), ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (Polynomial.algEquivAevalXAddC a).toRingHom ≫
      CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom =
        CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) a).toRingHom := by
    apply CommRingCat.hom_ext
    exact affine_polynomial c a
  rw [he]
  rw [projectiveLinePolynomial_coeff, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The polynomial chart after coefficient change is the corresponding pullback chart. -/
theorem projectiveBaseChange_polynomial_chart (f : K →+* R) :
    projectiveLinePolynomialChart R ⟨0⟩ ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom =
      Limits.pullback.lift (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
          projectiveLinePolynomialChart K ⟨0⟩) (by
            rw [Category.assoc, projectiveLinePolynomialChart_base, ← Spec.map_comp,
              ← Spec.map_comp]
            congr 1
            ext r
            simp) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, projectiveBaseChange_fst,
      projectiveLinePolynomialChart_base, Limits.pullback.lift_fst]
  · rw [Category.assoc, projectiveBaseChange_snd,
      projectiveLinePolynomial_coeff, Limits.pullback.lift_snd]

end SchubertGeometry

end

/-! # Relative lifts of affine projective families -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
universe u
variable {K R : Type u} [CommRing K] [CommRing R]

private theorem projective_base_ext {T : Scheme.{u}} (f : K →+* R)
    (p q : T ⟶ projectiveScheme R (ULift.{u} (Fin 2)))
    (hp : p ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      q ≫ projectiveToSpec R (ULift.{u} (Fin 2)))
    (hq : p ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      q ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f) : p = q := by
  apply (cancel_mono (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom).mp
  apply Limits.pullback.hom_ext
  · simpa only [Category.assoc, projectiveBaseChange_fst] using hp
  · simpa only [Category.assoc, projectiveBaseChange_snd] using hq

private def relativeAffineFamily (f : K →+* R) (c : Rˣ) (a : R) :
    projectiveScheme R (ULift.{u} (Fin 2)) ⟶ projectiveScheme R (ULift.{u} (Fin 2)) :=
  Limits.pullback.lift (projectiveToSpec R (ULift.{u} (Fin 2)))
    ((projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
      (projectiveAffineFamily f c a).left) (by
        have hw := (projectiveAffineFamily f c a).w
        change (projectiveAffineFamily f c a).left ≫ projectiveToSpec K _ =
          Limits.pullback.fst (Spec.map (CommRingCat.ofHom f))
            (projectiveToSpec K _) ≫ Spec.map (CommRingCat.ofHom f) at hw
        rw [Category.assoc, hw, ← Category.assoc, projectiveBaseChange_fst]) ≫
    (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv

private theorem relativeAffineFamily_eq (f : K →+* R) (c : Rˣ) (a : R) :
    relativeAffineFamily f c a =
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom := by
  have hf : (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
      projectiveToSpec R (ULift.{u} (Fin 2)) = Limits.pullback.fst _ _ :=
    (Iso.inv_comp_eq (projectiveBaseChange (ULift.{u} (Fin 2)) f)).mpr
      (projectiveBaseChange_fst (ULift.{u} (Fin 2)) f).symm
  have hs : (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) f = Limits.pullback.snd _ _ :=
    (Iso.inv_comp_eq (projectiveBaseChange (ULift.{u} (Fin 2)) f)).mpr
      (projectiveBaseChange_snd (ULift.{u} (Fin 2)) f).symm
  apply projective_base_ext f
  · rw [relativeAffineFamily, Category.assoc, hf, Limits.pullback.lift_fst,
      Category.assoc, projectiveLineTranslation_base, projectiveLineScaling_base]
  · rw [relativeAffineFamily, Category.assoc, hs, Limits.pullback.lift_snd]
    change (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
      (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f = _
    rw [Iso.hom_inv_id_assoc]
    exact (Category.assoc (projectiveLineScalingIso c).hom
      (projectiveLineTranslationIso a).hom (projectiveCoeffMap (ULift.{u} (Fin 2)) f)).symm


/-- The relative lift of an affine projective family is its coefficient-ring automorphism. -/
theorem projectiveAffineFamily_relative (f : K →+* R) (c : Rˣ) (a : R) :
    Limits.pullback.lift (projectiveToSpec R (ULift.{u} (Fin 2)))
      ((projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
        (projectiveAffineFamily f c a).left) (by
          have hw := (projectiveAffineFamily f c a).w
          change (projectiveAffineFamily f c a).left ≫ projectiveToSpec K _ =
            Limits.pullback.fst (Spec.map (CommRingCat.ofHom f))
              (projectiveToSpec K _) ≫ Spec.map (CommRingCat.ofHom f) at hw
          rw [Category.assoc, hw, ← Category.assoc, projectiveBaseChange_fst]) ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv =
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom :=
  relativeAffineFamily_eq f c a

end SchubertGeometry
end

/-! # Coefficient change for affine projective automorphisms -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R A ι : Type u} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem matrix_ring_natural (f : R →+* A) (m : Matrix ι ι R) :
    (projectiveMatrixHom (K := A) (m.map f)).toRingHom.comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (projectiveMatrixHom (K := R) m).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change projectiveMatrixHom (K := A) (m.map f) (MvPolynomial.map f (C r)) =
      MvPolynomial.map f (projectiveMatrixHom (K := R) m (C r))
    simp only [MvPolynomial.map_C, projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
  · intro i
    change projectiveMatrixHom (K := A) (m.map f) (MvPolynomial.map f (X i)) =
      MvPolynomial.map f (projectiveMatrixHom (K := R) m (X i))
    simp only [MvPolynomial.map_X, projectiveMatrixHom_X, map_sum, map_mul,
      MvPolynomial.map_C, Matrix.map_apply]

private theorem matrix_coeff_natural (f : R →+* A)
    (m : Matrix.GeneralLinearGroup ι R) (n : Matrix.GeneralLinearGroup ι A)
    (h : (n : Matrix ι ι A) = (m : Matrix ι ι R).map f) :
    projectiveMatrixMap (R := A) n ≫ projectiveCoeffMap ι f =
      projectiveCoeffMap ι f ≫ projectiveMatrixMap (R := R) m := by
  unfold projectiveMatrixMap projectiveCoeffMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  change (projectiveMatrixHom (K := A) (n : Matrix ι ι A)).toRingHom.comp
      (MvPolynomial.map f) =
    (MvPolynomial.map f).comp (projectiveMatrixHom (K := R) (m : Matrix ι ι R)).toRingHom
  rw [h]
  exact matrix_ring_natural f (m : Matrix ι ι R)

private abbrev lineIndex : Type u := ULift.{u} (Fin 2)

private def translationMatrix (a : R) : Matrix.GeneralLinearGroup lineIndex.{u} R :=
  Matrix.GeneralLinearGroup.transvection
    (⟨1⟩ : lineIndex.{u}) ⟨0⟩ (by decide) a

private def scalingMatrix (c : Rˣ) : Matrix.GeneralLinearGroup lineIndex.{u} R where
  val := Matrix.diagonal (fun i => if i.down = 0 then 1 else (c : R))
  inv := Matrix.diagonal (fun i => if i.down = 0 then 1 else (↑(c⁻¹) : R))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    split_ifs <;> simp

private theorem translation_matrix_map (f : R →+* A) (a : R) :
    (translationMatrix (f a) : Matrix lineIndex.{u} lineIndex.{u} A) =
      (translationMatrix a : Matrix lineIndex.{u} lineIndex.{u} R).map f := by
  ext i j
  simp [translationMatrix, Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
    Matrix.map_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

private theorem scaling_matrix_map (f : R →+* A) (c : Rˣ) :
    (scalingMatrix (Units.map f.toMonoidHom c) : Matrix lineIndex.{u} lineIndex.{u} A) =
      (scalingMatrix c : Matrix lineIndex.{u} lineIndex.{u} R).map f := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.down = 0 <;> simp [scalingMatrix, Matrix.diagonal, Matrix.map_apply, hi]
  · simp [scalingMatrix, Matrix.diagonal, Matrix.map_apply, hij]

private theorem translation_coeff (f : R →+* A) (a : R) :
    (projectiveLineTranslationIso (f a)).hom ≫ projectiveCoeffMap lineIndex.{u} f =
      projectiveCoeffMap lineIndex.{u} f ≫ (projectiveLineTranslationIso a).hom :=
  matrix_coeff_natural f (translationMatrix a) (translationMatrix (f a))
    (translation_matrix_map f a)

private theorem scaling_coeff (f : R →+* A) (c : Rˣ) :
    (projectiveLineScalingIso (Units.map f.toMonoidHom c)).hom ≫
        projectiveCoeffMap lineIndex.{u} f =
      projectiveCoeffMap lineIndex.{u} f ≫ (projectiveLineScalingIso c).hom :=
  matrix_coeff_natural f (scalingMatrix c) (scalingMatrix (Units.map f.toMonoidHom c))
    (scaling_matrix_map f c)

/-- Affine projective automorphisms commute with arbitrary change of coefficient ring. -/
theorem projectiveAffine_coeff (f : R →+* A) (c : Rˣ) (a : R) :
    ((projectiveLineScalingIso (Units.map f.toMonoidHom c)).hom ≫
      (projectiveLineTranslationIso (f a)).hom) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom := by
  rw [Category.assoc, translation_coeff, ← Category.assoc, scaling_coeff, Category.assoc]

end SchubertGeometry
end
