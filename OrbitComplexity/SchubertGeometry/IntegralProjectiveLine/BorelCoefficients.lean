import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelBaseChange
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Coefficients of Borel transition maps -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Opposite
open CartesianMonoidalCategory MonoidalCategory MvPolynomial
open scoped CategoryTheory.MonObj
universe u v w

private def actionTwist {D : Type v} [Category.{w} D] [CartesianMonoidalCategory D]
    {H S Y : D} [MonObj H] [ModObj H Y] (beta0 : S ⟶ H) : S ⊗ Y ⟶ S ⊗ Y :=
  lift (fst S Y) ((fst S Y ≫ beta0) • snd S Y)

private theorem actionTwist_mul {D : Type v} [Category.{w} D] [CartesianMonoidalCategory D]
    {H S Y : D} [MonObj H] [ModObj H Y] (beta0 beta1 : S ⟶ H) :
    actionTwist (Y := Y) beta0 ≫ actionTwist beta1 = actionTwist (beta1 * beta0) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [actionTwist, Category.assoc, lift_fst]
  · simp only [actionTwist, Category.assoc, lift_snd]
    rw [ModObj.comp_smul, lift_fst_assoc, lift_snd, ← mul_smul, ← MonObj.comp_mul]

private theorem actionTwist_one {D : Type v} [Category.{w} D] [CartesianMonoidalCategory D]
    {H S Y : D} [MonObj H] [ModObj H Y] : actionTwist (H := H) (S := S) (Y := Y) 1 = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [actionTwist, lift_fst, Category.id_comp]
  · simp only [actionTwist, lift_snd, MonObj.comp_one, one_smul, Category.id_comp]

private theorem transportedTwist_mul {D : Type v} [Category.{w} D]
    [CartesianMonoidalCategory D] {C : Type*} [Category C] (U : D ⥤ C)
    {H S Y : D} [MonObj H] [ModObj H Y] {P : C} (e : U.obj (S ⊗ Y) ≅ P)
    (F : (S ⟶ H) → (P ⟶ P))
    (hF : ∀ beta0, e.inv ≫ U.map (actionTwist beta0) ≫ e.hom = F beta0)
    (beta0 beta1 : S ⟶ H) :
    F beta0 ≫ F beta1 = F (beta1 * beta0) := by
  calc
    _ = e.inv ≫ U.map (actionTwist beta0 ≫ actionTwist beta1) ≫ e.hom := by
      rw [← hF beta0, ← hF beta1]
      simp only [U.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
    _ = F (beta1 * beta0) := by rw [actionTwist_mul, hF]

private theorem transportedTwist_one {D : Type v} [Category.{w} D]
    [CartesianMonoidalCategory D] {C : Type*} [Category C] (U : D ⥤ C)
    {H S Y : D} [MonObj H] [ModObj H Y] {P : C} (e : U.obj (S ⊗ Y) ≅ P)
    (F : (S ⟶ H) → (P ⟶ P))
    (hF : ∀ beta0, e.inv ≫ U.map (actionTwist beta0) ≫ e.hom = F beta0) : F 1 = 𝟙 _ := by
  rw [← hF 1, actionTwist_one, U.map_id, Category.id_comp, Iso.inv_hom_id]

section Affine
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R idx : Type u} [CommRing R] [Fintype idx] [DecidableEq idx]

omit [DecidableEq idx] in
private theorem matrixHom_comp (a b : Matrix idx idx R) :
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
    projectiveMatrixHom (K := R) (1 : Matrix idx idx R) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule idx R) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change projectiveMatrixHom (K := R) (1 : Matrix idx idx R) (MvPolynomial.C r) = MvPolynomial.C r
    simp only [projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
  · intro i
    change projectiveMatrixHom (1 : Matrix idx idx R) (MvPolynomial.X i) = MvPolynomial.X i
    simp [projectiveMatrixHom_X, Matrix.one_apply]

private theorem matrixMap_comp (a b : Matrix.GeneralLinearGroup idx R) :
    projectiveMatrixMap (R := R) a ≫ projectiveMatrixMap (R := R) b =
      projectiveMatrixMap (R := R) (b * a) := by
  unfold projectiveMatrixMap
  rw [← Proj.map_comp]
  congr 1
  exact matrixHom_comp _ _

private theorem matrixMap_one :
    projectiveMatrixMap (R := R) (1 : Matrix.GeneralLinearGroup idx R) =
      𝟙 (projectiveScheme R idx) := by
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

private theorem projectiveAffine_comp (c d : Rˣ) (a b : R) :
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

private theorem projectiveAffine_one :
    (projectiveLineScalingIso (1 : Rˣ)).hom ≫
        (projectiveLineTranslationIso (0 : R)).hom =
      𝟙 (projectiveScheme R (ULift.{u} (Fin 2))) := by
  change projectiveMatrixMap (scalingMatrix (1 : Rˣ)) ≫
    projectiveMatrixMap (translationMatrix (0 : R)) = _
  rw [matrixMap_comp, affineMatrix_one, matrixMap_one]

end Affine

variable {R : Type u} [CommRing R]

private theorem affine_chart (c : Rˣ) (a : R) :
    projectiveLinePolynomialChart R ⟨0⟩ ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom =
      Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivCMulXAddC (c : R) a).toRingHom) ≫
          projectiveLinePolynomialChart R ⟨0⟩ := by
  have he : CommRingCat.ofHom (Polynomial.algEquivAevalXAddC a).toRingHom ≫
      CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom =
        CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) a).toRingHom := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  rw [← reassoc_of% (projectiveLineScaling_chart c),
    ← projectiveLineTranslation_chart a, ← Category.assoc, ← Spec.map_comp, he]

private theorem affine_parameters_injective (c d : Rˣ) (a b : R)
    (h : (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom =
      (projectiveLineScalingIso d).hom ≫ (projectiveLineTranslationIso b).hom) :
    c = d ∧ a = b := by
  have hs := congrArg (fun m => projectiveLinePolynomialChart R ⟨0⟩ ≫ m) h
  rw [affine_chart, affine_chart] at hs
  have hr := Spec.map_injective ((cancel_mono (projectiveLinePolynomialChart R ⟨0⟩)).mp hs)
  have hx := congrArg (fun f : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (Polynomial R) =>
    f.hom Polynomial.X) hr
  have hzero := congrArg (fun p : Polynomial R => p.coeff 0) hx
  have hone := congrArg (fun p : Polynomial R => p.coeff 1) hx
  refine ⟨Units.ext ?_, ?_⟩
  · simpa using hone
  · simpa using hzero


private theorem coefficientPair_inv {B : Type v} [Group B] (p : B → Rˣ × R)
    (hmul : ∀ x y, (p (y * x)).1 = (p y).1 * (p x).1 ∧
      (p (y * x)).2 = ((p y).1 : R) * (p x).2 + (p y).2)
    (hone : (p 1).1 = 1 ∧ (p 1).2 = 0) (x : B) :
    (p x⁻¹).1 = (p x).1⁻¹ ∧
      (p x⁻¹).2 = -((↑((p x).1⁻¹) : R) * (p x).2) := by
  have hc := (hmul x x⁻¹).1
  have ha := (hmul x x⁻¹).2
  rw [inv_mul_cancel, hone.1] at hc
  rw [inv_mul_cancel, hone.2] at ha
  have hci : (p x⁻¹).1 = (p x).1⁻¹ := by
    calc
      _ = ((p x⁻¹).1 * (p x).1) * (p x).1⁻¹ := by simp [mul_assoc]
      _ = (p x).1⁻¹ := by rw [← hc, one_mul]
  refine ⟨hci, ?_⟩
  calc
    (p x⁻¹).2 = (((p x⁻¹).1 : R) * (p x).2 + (p x⁻¹).2) -
        ((p x⁻¹).1 : R) * (p x).2 := by ring
    _ = -(((p x⁻¹).1 : R) * (p x).2) := by rw [← ha]; simp
    _ = _ := by rw [hci]

section Borel
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def borelCoefficients (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) : Aˣ × A :=
  let f := simpleBorelCoefficientMap G i A beta
  ⟨Units.map f.toRingHom.toMonoidHom (simpleRootCoefficient G i),
    f ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
      simpleRootParameter G)⟩

private def borelAffine (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    projectiveScheme A (ULift.{u} (Fin 2)) ⟶ projectiveScheme A (ULift.{u} (Fin 2)) :=
  (projectiveLineScalingIso (borelCoefficients G i A beta).1).hom ≫
    (projectiveLineTranslationIso (borelCoefficients G i A beta).2).hom

private theorem borelAffine_mul (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta0 beta1 : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    borelAffine G i A beta0 ≫ borelAffine G i A beta1 = borelAffine G i A (beta1 * beta0) := by
  let := simpleBorelAction G i
  exact transportedTwist_mul (Over.forget (Spec (.of K))) (simpleBorelLineIso G i A)
    (borelAffine G i A) (fun beta => simpleBorelAction_relative G i A beta) beta0 beta1

private theorem borelAffine_one (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    borelAffine G i A 1 = 𝟙 _ := by
  let := simpleBorelAction G i
  exact transportedTwist_one (Over.forget (Spec (.of K))) (simpleBorelLineIso G i A)
    (borelAffine G i A) (fun beta => simpleBorelAction_relative G i A beta)

private theorem borelCoefficients_mul (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta0 beta1 : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    (borelCoefficients G i A (beta1 * beta0)).1 =
        (borelCoefficients G i A beta1).1 * (borelCoefficients G i A beta0).1 ∧
      (borelCoefficients G i A (beta1 * beta0)).2 =
        ((borelCoefficients G i A beta1).1 : A) * (borelCoefficients G i A beta0).2 +
          (borelCoefficients G i A beta1).2 := by
  apply affine_parameters_injective
  exact (borelAffine_mul G i A beta0 beta1).symm.trans (projectiveAffine_comp _ _ _ _)

private theorem borelCoefficients_one (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    (borelCoefficients G i A 1).1 = 1 ∧ (borelCoefficients G i A 1).2 = 0 := by
  apply affine_parameters_injective
  exact (borelAffine_one G i A).trans (projectiveAffine_one (R := A)).symm

private theorem borelCoefficients_inv (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    (borelCoefficients G i A beta⁻¹).1 = (borelCoefficients G i A beta).1⁻¹ ∧
      (borelCoefficients G i A beta⁻¹).2 =
        -((↑((borelCoefficients G i A beta).1⁻¹) : A) * (borelCoefficients G i A beta).2) := by
  exact coefficientPair_inv (borelCoefficients G i A)
    (borelCoefficients_mul G i A) (borelCoefficients_one G i A) beta

private theorem borelCoefficients_cocycle (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (beta01 beta12 beta02 : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver)
    (hbeta : beta02 = beta12 * beta01) :
    (borelCoefficients G i A beta02).1 =
        (borelCoefficients G i A beta12).1 * (borelCoefficients G i A beta01).1 ∧
      (borelCoefficients G i A beta02).2 =
        ((borelCoefficients G i A beta12).1 : A) * (borelCoefficients G i A beta01).2 +
          (borelCoefficients G i A beta12).2 := by
  rw [hbeta]
  exact borelCoefficients_mul G i A beta01 beta12


/-- Borel arrows have affine coefficients satisfying identity, product, inverse and cocycle laws. -/
theorem simpleBorelCoefficient_laws (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    let c := fun beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver =>
      Units.map (simpleBorelCoefficientMap G i A beta).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let a := fun beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver =>
      (simpleBorelCoefficientMap G i A beta)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G)
    (c 1 = 1 ∧ a 1 = 0) ∧
      (∀ beta0 beta1, c (beta1 * beta0) = c beta1 * c beta0 ∧
        a (beta1 * beta0) = (c beta1 : A) * a beta0 + a beta1) ∧
      (∀ beta, c beta⁻¹ = (c beta)⁻¹ ∧
        a beta⁻¹ = -((↑((c beta)⁻¹) : A) * a beta)) ∧
      (∀ beta01 beta12 beta02, beta02 = beta12 * beta01 →
        c beta02 = c beta12 * c beta01 ∧
          a beta02 = (c beta12 : A) * a beta01 + a beta12) := by
  exact ⟨borelCoefficients_one G i A, borelCoefficients_mul G i A,
    borelCoefficients_inv G i A, borelCoefficients_cocycle G i A⟩

end Borel
end SchubertGeometry
end
