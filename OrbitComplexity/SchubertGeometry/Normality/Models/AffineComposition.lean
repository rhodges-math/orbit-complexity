import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import Mathlib.Tactic.FinCases

/-! # Composition and inverses of affine projective transformations -/

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory GroupActions MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem matrixHom_comp (a b : Matrix ι ι R) :
    (projectiveMatrixHom (K := R) a).comp (projectiveMatrixHom (K := R) b) =
      projectiveMatrixHom (K := R) (b * a) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change projectiveMatrixHom (K := R) a
      (projectiveMatrixHom (K := R) b (MvPolynomial.C r)) =
        projectiveMatrixHom (K := R) (b * a) (MvPolynomial.C r)
    simp only [projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
  · intro i
    change projectiveMatrixHom (K := R) a
      (projectiveMatrixHom (K := R) b (MvPolynomial.X i)) =
        projectiveMatrixHom (K := R) (b * a) (MvPolynomial.X i)
    simp only [projectiveMatrixHom_X, map_sum, map_mul,
      projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
    change (∑ j, MvPolynomial.C (b i j) *
        ∑ k, MvPolynomial.C (a j k) * MvPolynomial.X k) =
      ∑ k, MvPolynomial.C (∑ j, b i j * a j k) * MvPolynomial.X k
    trans ∑ k, ∑ j, MvPolynomial.C (b i j) *
      (MvPolynomial.C (a j k) * MvPolynomial.X k)
    · rw [← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.mul_sum _ _ _
    · apply Finset.sum_congr rfl
      intro k hk
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul, mul_assoc]

private theorem matrixHom_one :
    projectiveMatrixHom (K := R) (1 : Matrix ι ι R) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule ι R) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change projectiveMatrixHom (K := R) (1 : Matrix ι ι R) (MvPolynomial.C r) = MvPolynomial.C r
    simp only [projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
  · intro i
    change projectiveMatrixHom (1 : Matrix ι ι R) (MvPolynomial.X i) = MvPolynomial.X i
    simp [projectiveMatrixHom_X, Matrix.one_apply]

private theorem matrixMap_comp (a b : Matrix.GeneralLinearGroup ι R) :
    projectiveMatrixMap (R := R) a ≫ projectiveMatrixMap (R := R) b =
      projectiveMatrixMap (R := R) (b * a) := by
  unfold projectiveMatrixMap
  rw [← Proj.map_comp]
  congr 1
  exact matrixHom_comp _ _

private theorem matrixMap_one :
    projectiveMatrixMap (R := R) (1 : Matrix.GeneralLinearGroup ι R) =
      𝟙 (projectiveScheme R ι) := by
  unfold projectiveMatrixMap
  rw [← Proj.map_id]
  congr 1
  exact matrixHom_one

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

private theorem sum_line (f : lineIndex.{u} → R) :
    ∑ i, f i = f ⟨0⟩ + f ⟨1⟩ := by
  have hu : (Finset.univ : Finset lineIndex.{u}) = {⟨0⟩, ⟨1⟩} := by
    ext ⟨i⟩
    fin_cases i <;> simp
  rw [hu]
  simp

private theorem affineMatrix_mul (c d : Rˣ) (a b : R) :
    (translationMatrix b * scalingMatrix d) *
        (translationMatrix a * scalingMatrix c) =
      translationMatrix ((d : R) * a + b) * scalingMatrix (d * c) := by
  apply Units.ext
  ext ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [translationMatrix, scalingMatrix, Matrix.GeneralLinearGroup.transvection,
      Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal,
      Matrix.mul_apply, sum_line, mul_add, add_mul, mul_assoc, add_comm]

private theorem affineMatrix_one :
    translationMatrix (0 : R) * scalingMatrix (1 : Rˣ) = 1 := by
  apply Units.ext
  ext ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [translationMatrix, scalingMatrix, Matrix.GeneralLinearGroup.transvection,
      Matrix.transvection, Matrix.one_apply, Matrix.diagonal,
      Matrix.mul_apply]

/-- Chronological affine transformations multiply their units and translate the first parameter. -/
theorem projectiveAffine_comp (c d : Rˣ) (a b : R) :
    ((projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom) ≫
        ((projectiveLineScalingIso d).hom ≫ (projectiveLineTranslationIso b).hom) =
      (projectiveLineScalingIso (d * c)).hom ≫
        (projectiveLineTranslationIso ((d : R) * a + b)).hom := by
  change (projectiveMatrixMap (scalingMatrix c) ≫ projectiveMatrixMap (translationMatrix a)) ≫
      (projectiveMatrixMap (scalingMatrix d) ≫ projectiveMatrixMap (translationMatrix b)) =
    projectiveMatrixMap (scalingMatrix (d * c)) ≫
      projectiveMatrixMap (translationMatrix ((d : R) * a + b))
  simp only [matrixMap_comp]
  rw [affineMatrix_mul]

/-- The affine transformation with unit one and parameter zero is the identity scheme map. -/
theorem projectiveAffine_one :
    (projectiveLineScalingIso (1 : Rˣ)).hom ≫
        (projectiveLineTranslationIso (0 : R)).hom =
      𝟙 (projectiveScheme R (ULift.{u} (Fin 2))) := by
  change projectiveMatrixMap (scalingMatrix (1 : Rˣ)) ≫
    projectiveMatrixMap (translationMatrix (0 : R)) = _
  rw [matrixMap_comp, affineMatrix_one, matrixMap_one]

/-- The inverse affine transformation has reciprocal unit and rescaled negative parameter. -/
theorem projectiveAffine_inv (c : Rˣ) (a : R) :
    ((projectiveLineScalingIso c) ≪≫ projectiveLineTranslationIso a).inv =
      (projectiveLineScalingIso c⁻¹).hom ≫
        (projectiveLineTranslationIso (-((↑(c⁻¹) : R) * a))).hom := by
  let e := (projectiveLineScalingIso c) ≪≫ projectiveLineTranslationIso a
  change e.inv = _
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id]
  change 𝟙 _ =
    ((projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom) ≫
      ((projectiveLineScalingIso c⁻¹).hom ≫
        (projectiveLineTranslationIso (-((↑(c⁻¹) : R) * a))).hom)
  rw [projectiveAffine_comp]
  simpa only [inv_mul_cancel, add_neg_cancel] using (projectiveAffine_one (R := R)).symm

end
end SchubertGeometry
