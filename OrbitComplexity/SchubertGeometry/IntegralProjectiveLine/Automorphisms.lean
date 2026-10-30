import OrbitComplexity.GroupActions.Representations.ProjectiveMatrix
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsInverse
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Affine-coordinate automorphisms of the projective line -/

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

private def matrixIso (a : Matrix.GeneralLinearGroup ι R) :
    projectiveScheme R ι ≅ projectiveScheme R ι where
  hom := projectiveMatrixMap a
  inv := projectiveMatrixMap a⁻¹
  hom_inv_id := by rw [matrixMap_comp, inv_mul_cancel, matrixMap_one]
  inv_hom_id := by rw [matrixMap_comp, mul_inv_cancel, matrixMap_one]

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

/-- The unipotent matrix fixing the first coordinate gives a projective translation. -/
def projectiveLineTranslationIso (a : R) :
    projectiveScheme R (ULift.{u} (Fin 2)) ≅ projectiveScheme R (ULift.{u} (Fin 2)) :=
  matrixIso (translationMatrix a)

/-- Scaling the second homogeneous coordinate by a unit gives a projective automorphism. -/
def projectiveLineScalingIso (c : Rˣ) :
    projectiveScheme R (ULift.{u} (Fin 2)) ≅ projectiveScheme R (ULift.{u} (Fin 2)) :=
  matrixIso (scalingMatrix c)


/-- Projective translation preserves the coefficient structure map. -/
theorem projectiveLineTranslation_base (a : R) :
    (projectiveLineTranslationIso a).hom ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec R (ULift.{u} (Fin 2)) := by
  change projectiveMatrixMap (R := R) (translationMatrix a) ≫
    projectiveToSpec R lineIndex.{u} = projectiveToSpec R lineIndex.{u}
  simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id] using projectiveMatrixMap_toSpec (R := R) (translationMatrix a)

/-- Diagonal scaling preserves the coefficient structure map. -/
theorem projectiveLineScaling_base (c : Rˣ) :
    (projectiveLineScalingIso c).hom ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec R (ULift.{u} (Fin 2)) := by
  change projectiveMatrixMap (R := R) (scalingMatrix c) ≫
    projectiveToSpec R lineIndex.{u} = projectiveToSpec R lineIndex.{u}
  simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id] using projectiveMatrixMap_toSpec (R := R) (scalingMatrix c)

private theorem translation_X0 (a : R) :
    projectiveMatrixHom (K := R)
      (translationMatrix a : Matrix lineIndex.{u} lineIndex.{u} R) (X ⟨0⟩) = X ⟨0⟩ := by
  simp [projectiveMatrixHom_X, translationMatrix, Matrix.GeneralLinearGroup.transvection,
    Matrix.transvection, Matrix.one_apply]

private theorem translation_X1 (a : R) :
    projectiveMatrixHom (K := R)
      (translationMatrix a : Matrix lineIndex.{u} lineIndex.{u} R) (X ⟨1⟩) =
        X ⟨1⟩ + C a * X ⟨0⟩ := by
  simp [projectiveMatrixHom_X, translationMatrix, Matrix.GeneralLinearGroup.transvection,
    Matrix.transvection, Matrix.single_apply, Matrix.one_apply, add_mul,
    Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (⟨0⟩ : lineIndex.{u})]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
  · simp

private theorem scaling_X (c : Rˣ) (i : lineIndex.{u}) :
    projectiveMatrixHom (K := R)
      (scalingMatrix c : Matrix lineIndex.{u} lineIndex.{u} R) (X i) =
        C (if i.down = 0 then 1 else (c : R)) * X i := by
  simp only [projectiveMatrixHom_X, scalingMatrix, Matrix.diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · simp

private theorem scaling_X0 (c : Rˣ) :
    projectiveMatrixHom (K := R)
      (scalingMatrix c : Matrix lineIndex.{u} lineIndex.{u} R) (X ⟨0⟩) = X ⟨0⟩ := by
  simpa using scaling_X c (⟨0⟩ : lineIndex.{u})

private theorem scaling_X1 (c : Rˣ) :
    projectiveMatrixHom (K := R)
      (scalingMatrix c : Matrix lineIndex.{u} lineIndex.{u} R) (X ⟨1⟩) =
        C (c : R) * X ⟨1⟩ := by
  simpa using scaling_X c (⟨1⟩ : lineIndex.{u})

private abbrev lineGrade (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule lineIndex.{u} R

private def localizationMapAt (f : lineGrade R →+*ᵍ lineGrade R)
    (s t : MvPolynomial lineIndex.{u} R) (h : f s = t) :
    HomogeneousLocalization.Away (lineGrade R) s →+*
      HomogeneousLocalization.Away (lineGrade R) t :=
  HomogeneousLocalization.map f (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by rw [map_pow, h]⟩)

private theorem localization_square (f : lineGrade R →+*ᵍ lineGrade R)
    (hf : HomogeneousIdeal.irrelevant (lineGrade R) ≤
      (HomogeneousIdeal.irrelevant (lineGrade R)).map f)
    (s t : MvPolynomial lineIndex.{u} R) (hs : s ∈ lineGrade R 1)
    (ht : t ∈ lineGrade R 1) (h : f s = t) :
    Proj.awayι (lineGrade R) t ht Nat.zero_lt_one ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (localizationMapAt f s t h)) ≫
        Proj.awayι (lineGrade R) s hs Nat.zero_lt_one := by
  subst t
  simpa only [localizationMapAt, HomogeneousLocalization.Away.map] using
    Proj.awayι_comp_map f hf Nat.zero_lt_one s hs

private def coordinateLocalization (f : lineGrade R →+*ᵍ lineGrade R)
    (hf : f (X (⟨0⟩ : lineIndex.{u})) = X ⟨0⟩) :
    HomogeneousLocalization.Away (lineGrade R) (X (⟨0⟩ : lineIndex.{u})) →+*
      HomogeneousLocalization.Away (lineGrade R) (X (⟨0⟩ : lineIndex.{u})) :=
  localizationMapAt f _ _ hf

private theorem coordinateLocalization_mk (f : lineGrade R →+*ᵍ lineGrade R)
    (hf : f (X (⟨0⟩ : lineIndex.{u})) = X ⟨0⟩) (n : ℕ)
    (q : MvPolynomial lineIndex.{u} R) (hq : q ∈ lineGrade R (n • 1)) :
    coordinateLocalization f hf
        (HomogeneousLocalization.Away.mk (lineGrade R)
          (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) n q hq) =
      HomogeneousLocalization.Away.mk (lineGrade R)
        (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) n (f q) (f.map_mem hq) := by
  unfold coordinateLocalization localizationMapAt HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = Localization.mk _ _
  congr 1
  apply Subtype.ext
  simp only [map_pow, hf]


private def chart0Ring : Polynomial R ≃+*
    HomogeneousLocalization.Away (lineGrade R) (X (⟨0⟩ : lineIndex.{u})) :=
  (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩}).toRingEquiv.symm.trans
    (projectiveChartRingEquiv R lineIndex.{u} ⟨0⟩)

private theorem chart0Ring_X :
    chart0Ring (R := R) Polynomial.X =
      HomogeneousLocalization.Away.isLocalizationElem
        (isHomogeneous_X R (⟨0⟩ : lineIndex.{u}))
        (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) := by
  change projectiveChartRingEquiv R lineIndex.{u} ⟨0⟩
    ((MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩}).symm Polynomial.X) = _
  rw [← show (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩})
    (X ⟨⟨1⟩, by decide⟩) = Polynomial.X from by simp,
    AlgEquiv.symm_apply_apply, projectiveChartRingEquiv_X]

private theorem chart0Ring_symm_mk (n : ℕ) (q : MvPolynomial lineIndex.{u} R)
    (hq : q ∈ lineGrade R (n • 1)) :
    (chart0Ring (R := R)).symm
        (HomogeneousLocalization.Away.mk (lineGrade R)
          (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) n q hq) =
      (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩})
        (projectiveDehomogenize R lineIndex.{u} ⟨0⟩ q) := by
  change (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩})
    ((projectiveChartRingEquiv R lineIndex.{u} ⟨0⟩).symm _) = _
  rw [projectiveChartRingEquiv_symm_mk]

private theorem chart0Ring_C (r : R) :
    chart0Ring (Polynomial.C r) =
      HomogeneousLocalization.Away.mk (lineGrade R)
        (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) 0 (C r)
        (by
          change (C r).IsHomogeneous (0 • (1 : ℕ))
          simpa only [zero_smul] using isHomogeneous_C lineIndex.{u} r) := by
  have hc := (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩}).symm.commutes r
  change (MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩}).symm
    (Polynomial.C r) = C r at hc
  change projectiveChartRingEquiv R lineIndex.{u} ⟨0⟩
    ((MvPolynomial.uniqueAlgEquiv R {i : lineIndex.{u} // i ≠ ⟨0⟩}).symm (Polynomial.C r)) = _
  rw [hc, projectiveChartRingEquiv_C]
  rfl

private theorem chart0Ring_chart :
    projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) =
      Spec.map (CommRingCat.ofHom (chart0Ring (R := R)).symm.toRingHom) ≫
        Proj.awayι (lineGrade R) (X (⟨0⟩ : lineIndex.{u}))
          (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) Nat.zero_lt_one := by
  unfold projectiveLinePolynomialChart projectiveLinePolynomialIso projectiveChartIso chart0Ring
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.op_hom, Iso.op_inv, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private theorem ringConjugation_cancel {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : B →+* B) (t : A →+* A)
    (he : e.symm.toRingHom.comp (h.comp e.toRingHom) = t) :
    t.comp e.symm.toRingHom = e.symm.toRingHom.comp h := by
  apply RingHom.ext
  intro z
  have hh := DFunLike.congr_fun he (e.symm z)
  change e.symm (h (e (e.symm z))) = t (e.symm z) at hh
  rw [e.apply_symm_apply] at hh
  exact hh.symm

private def translationLocalization (a : R) :=
  coordinateLocalization
    (projectiveMatrixHom (K := R) (translationMatrix a : Matrix lineIndex.{u} lineIndex.{u} R))
    (translation_X0 a)


private theorem chart0Ring_translate (a : R) :
    (chart0Ring (R := R)).symm.toRingHom.comp
        ((translationLocalization a).comp (chart0Ring (R := R)).toRingHom) =
      (Polynomial.algEquivAevalXAddC a).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change (chart0Ring (R := R)).symm
      (translationLocalization a (chart0Ring (Polynomial.C r))) =
        Polynomial.algEquivAevalXAddC a (Polynomial.C r)
    rw [chart0Ring_C, translationLocalization, coordinateLocalization_mk, chart0Ring_symm_mk]
    simp [projectiveMatrixHom_C, projectiveDehomogenize]
  · change (chart0Ring (R := R)).symm
      (translationLocalization a (chart0Ring Polynomial.X)) =
        Polynomial.algEquivAevalXAddC a Polynomial.X
    rw [chart0Ring_X]
    unfold HomogeneousLocalization.Away.isLocalizationElem
    rw [translationLocalization, coordinateLocalization_mk, chart0Ring_symm_mk]
    simp [translation_X1, projectiveDehomogenize]

private def scalingLocalization (c : Rˣ) :=
  coordinateLocalization
    (projectiveMatrixHom (K := R) (scalingMatrix c : Matrix lineIndex.{u} lineIndex.{u} R))
    (scaling_X0 c)


private theorem chart0Ring_scale (c : Rˣ) :
    (chart0Ring (R := R)).symm.toRingHom.comp
        ((scalingLocalization c).comp (chart0Ring (R := R)).toRingHom) =
      (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change (chart0Ring (R := R)).symm
      (scalingLocalization c (chart0Ring (Polynomial.C r))) =
        Polynomial.algEquivCMulXAddC (c : R) 0 (Polynomial.C r)
    rw [chart0Ring_C, scalingLocalization, coordinateLocalization_mk, chart0Ring_symm_mk]
    simp [projectiveMatrixHom_C, projectiveDehomogenize]
  · change (chart0Ring (R := R)).symm
      (scalingLocalization c (chart0Ring Polynomial.X)) =
        Polynomial.algEquivCMulXAddC (c : R) 0 Polynomial.X
    rw [chart0Ring_X]
    unfold HomogeneousLocalization.Away.isLocalizationElem
    rw [scalingLocalization, coordinateLocalization_mk, chart0Ring_symm_mk]
    simp [scaling_X1, projectiveDehomogenize]

private theorem coordinate_chart (f : lineGrade R →+*ᵍ lineGrade R)
    (hf : HomogeneousIdeal.irrelevant (lineGrade R) ≤
      (HomogeneousIdeal.irrelevant (lineGrade R)).map f)
    (h0 : f (X (⟨0⟩ : lineIndex.{u})) = X ⟨0⟩) (t : Polynomial R →+* Polynomial R)
    (ht : (chart0Ring (R := R)).symm.toRingHom.comp
      ((coordinateLocalization f h0).comp (chart0Ring (R := R)).toRingHom) = t) :
    Spec.map (CommRingCat.ofHom t) ≫ projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) =
      projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) ≫ Proj.map f hf := by
  have heRing := ringConjugation_cancel (chart0Ring (R := R))
    (coordinateLocalization f h0) t ht
  rw [chart0Ring_chart, Category.assoc, localization_square f hf _ _
    (isHomogeneous_X R (⟨0⟩ : lineIndex.{u}))
    (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) h0]
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫
    Proj.awayι (lineGrade R) (X (⟨0⟩ : lineIndex.{u}))
      (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) Nat.zero_lt_one) heRing

/-- The triangular projective automorphism adds its parameter on the polynomial chart. -/
theorem projectiveLineTranslation_chart (a : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC a).toRingHom) ≫
        projectiveLinePolynomialChart R (⟨0⟩ : ULift.{u} (Fin 2)) =
      projectiveLinePolynomialChart R (⟨0⟩ : ULift.{u} (Fin 2)) ≫
        (projectiveLineTranslationIso a).hom := by
  change _ = _ ≫ projectiveMatrixMap (R := R) (translationMatrix a)
  unfold projectiveMatrixMap
  exact coordinate_chart _ _ (translation_X0 a) _ (chart0Ring_translate a)

/-- The diagonal projective automorphism multiplies its polynomial coordinate by a unit. -/
theorem projectiveLineScaling_chart (c : Rˣ) :
    Spec.map (CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom) ≫
        projectiveLinePolynomialChart R (⟨0⟩ : ULift.{u} (Fin 2)) =
      projectiveLinePolynomialChart R (⟨0⟩ : ULift.{u} (Fin 2)) ≫
        (projectiveLineScalingIso c).hom := by
  change _ = _ ≫ projectiveMatrixMap (R := R) (scalingMatrix c)
  unfold projectiveMatrixMap
  exact coordinate_chart _ _ (scaling_X0 c) _ (chart0Ring_scale c)

end
end SchubertGeometry
