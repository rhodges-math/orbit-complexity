import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveLine

/-! # The distinguished infinity section and homogeneous affine substitutions -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory AlgebraicGeometry GroupActions MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev lineIndex := ULift.{u} (Fin 2)
private abbrev pointIndex := ULift.{u} (Fin 1)
variable (R : Type u) [CommRing R]

private def pointEmbedding :
    homogeneousSubmodule lineIndex.{u} R →+*ᵍ homogeneousSubmodule pointIndex.{u} R where
  __ := (MvPolynomial.aeval
    (fun j : lineIndex.{u} => if j.down = 1 then X (⟨0⟩ : pointIndex.{u}) else 0) :
      MvPolynomial lineIndex.{u} R →ₐ[R] MvPolynomial pointIndex.{u} R).toRingHom
  map_mem {i} {p} hp := by
    change p.IsHomogeneous i at hp
    change (MvPolynomial.aeval
      (fun j : lineIndex.{u} => if j.down = 1 then
        (X (⟨0⟩ : pointIndex.{u}) : MvPolynomial pointIndex.{u} R) else 0) p).IsHomogeneous i
    have h : ∀ j : lineIndex.{u},
        (if j.down = 1 then (X (⟨0⟩ : pointIndex.{u}) : MvPolynomial pointIndex.{u} R)
          else 0).IsHomogeneous 1 := by
      intro j
      split_ifs
      · exact isHomogeneous_X R _
      · exact isHomogeneous_zero pointIndex.{u} R 1
    simpa only [one_mul] using hp.aeval _ h

private theorem pointEmbedding_X (j : lineIndex.{u}) :
    pointEmbedding R (X j) = if j.down = 1 then X (⟨0⟩ : pointIndex.{u}) else 0 :=
  MvPolynomial.aeval_X _ j

private theorem pointEmbedding_C (r : R) : pointEmbedding R (C r) = C r := by
  change MvPolynomial.aeval _ (C r) = _
  simp

private theorem pointEmbedding_irrelevant :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule pointIndex.{u} R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule lineIndex.{u} R)).map
        (pointEmbedding R) := by
  rw [← toIdeal_le_toIdeal_iff, projective_irrelevant_eq_span,
    HomogeneousIdeal.toIdeal_map]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hj : j = (⟨0⟩ : pointIndex.{u}) := Subsingleton.elim _ _
  subst j
  rw [← show pointEmbedding R (X (⟨1⟩ : lineIndex.{u})) = X (⟨0⟩ : pointIndex.{u})
    from by simp [pointEmbedding_X]]
  exact Ideal.mem_map_of_mem (pointEmbedding R) (HomogeneousIdeal.mem_irrelevant_of_mem _
    Nat.zero_lt_one (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})))

private def pointEmbeddingMap : projectiveScheme R pointIndex.{u} ⟶
    projectiveScheme R lineIndex.{u} :=
  Proj.map (pointEmbedding R) (pointEmbedding_irrelevant R)

private instance emptyRemaining : IsEmpty {j : pointIndex.{u} // j ≠ ⟨0⟩} :=
  ⟨fun j => j.property (Subsingleton.elim _ _)⟩

private theorem pointChart_isIso :
    IsIso (projectiveChartMap R pointIndex.{u} ⟨0⟩) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [projectiveChartMap_range]
  have h := Proj.iSup_basicOpen_eq_top (homogeneousSubmodule pointIndex.{u} R)
    (X : pointIndex.{u} → MvPolynomial pointIndex.{u} R)
    (projective_irrelevant_eq_span R pointIndex.{u}).le
  rw [iSup_unique] at h
  exact (congrArg (fun j : pointIndex.{u} =>
    Proj.basicOpen (homogeneousSubmodule pointIndex.{u} R) (X j))
      (Subsingleton.elim (default : pointIndex.{u}) ⟨0⟩)).symm.trans h

private theorem pointBase_isIso : IsIso (projectiveToSpec R pointIndex.{u}) := by
  let : IsIso (projectiveChartMap R pointIndex.{u} ⟨0⟩) := pointChart_isIso R
  have hC : CommRingCat.ofHom
      (C : R →+* MvPolynomial {j : pointIndex.{u} // j ≠ ⟨0⟩} R) =
      (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩}).toCommRingCatIso.inv := by
    rw [← isEmptyRingEquiv_symm_toRingHom]
    rfl
  have hc : IsIso (projectiveChartMap R pointIndex.{u} ⟨0⟩ ≫
      projectiveToSpec R pointIndex.{u}) := by
    rw [projectiveChartMap_toSpec, hC]
    infer_instance
  exact (isIso_comp_left_iff (projectiveChartMap R pointIndex.{u} ⟨0⟩) _).mp hc

private def pointChartRing :
    MvPolynomial {j : pointIndex.{u} // j ≠ ⟨0⟩} R ≃+*
      Away (homogeneousSubmodule pointIndex.{u} R) (X (⟨0⟩ : pointIndex.{u})) :=
  projectiveChartRingEquiv R pointIndex.{u} ⟨0⟩

private def lineChartRing :
    Polynomial R ≃+* Away (homogeneousSubmodule lineIndex.{u} R)
      (X (⟨1⟩ : lineIndex.{u})) :=
  (MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩}).toRingEquiv.symm.trans
    (projectiveChartRingEquiv R lineIndex.{u} ⟨1⟩)

private theorem pointChartMap_eq :
    projectiveChartMap R pointIndex.{u} ⟨0⟩ =
      Spec.map (CommRingCat.ofHom (pointChartRing R).symm.toRingHom) ≫
        Proj.awayι _ _ (isHomogeneous_X R (⟨0⟩ : pointIndex.{u})) Nat.zero_lt_one := by
  simp only [projectiveChartMap, projectiveChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Category.assoc]
  rfl

private theorem lineChartMap_eq :
    projectiveLinePolynomialChart R (⟨1⟩ : lineIndex.{u}) =
      Spec.map (CommRingCat.ofHom (lineChartRing R).symm.toRingHom) ≫
        Proj.awayι _ _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) Nat.zero_lt_one := by
  unfold projectiveLinePolynomialChart projectiveLinePolynomialIso projectiveChartIso lineChartRing
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.op_hom, Iso.op_inv, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private def embeddingAway :
    Away (homogeneousSubmodule lineIndex.{u} R) (X (⟨1⟩ : lineIndex.{u})) →+*
      Away (homogeneousSubmodule pointIndex.{u} R) (X (⟨0⟩ : pointIndex.{u})) :=
  HomogeneousLocalization.map (pointEmbedding R) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by rw [map_pow, pointEmbedding_X]; simp⟩)

private theorem embeddingAway_mk (n : ℕ) (q : MvPolynomial lineIndex.{u} R)
    (hq : q ∈ homogeneousSubmodule lineIndex.{u} R (n • 1)) :
    embeddingAway R (Away.mk _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) n q hq) =
      Away.mk _ (isHomogeneous_X R (⟨0⟩ : pointIndex.{u})) n
        (pointEmbedding R q) ((pointEmbedding R).map_mem hq) := by
  unfold embeddingAway Away.mk
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = Localization.mk _ _
  congr 1
  apply Subtype.ext
  change pointEmbedding R (X (⟨1⟩ : lineIndex.{u}) ^ n) =
    X (⟨0⟩ : pointIndex.{u}) ^ n
  rw [map_pow, pointEmbedding_X]
  simp

private theorem lineChartRing_X :
    lineChartRing R Polynomial.X = Away.isLocalizationElem
      (isHomogeneous_X R (⟨1⟩ : lineIndex.{u}))
      (isHomogeneous_X R (⟨0⟩ : lineIndex.{u})) := by
  change projectiveChartRingEquiv R lineIndex.{u} ⟨1⟩
    ((MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩}).symm Polynomial.X) = _
  rw [← show (MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩})
    (X ⟨⟨0⟩, by decide⟩) = Polynomial.X from by simp,
    AlgEquiv.symm_apply_apply, projectiveChartRingEquiv_X]

private theorem lineChartRing_C (r : R) :
    lineChartRing R (Polynomial.C r) =
      Away.mk _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) 0 (C r)
        (by
          change (C r).IsHomogeneous (0 • (1 : ℕ))
          simpa only [zero_smul] using isHomogeneous_C lineIndex.{u} r) := by
  have hc := (MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩}).symm.commutes r
  change (MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩}).symm
    (Polynomial.C r) = C r at hc
  change projectiveChartRingEquiv R lineIndex.{u} ⟨1⟩
    ((MvPolynomial.uniqueAlgEquiv R {j : lineIndex.{u} // j ≠ ⟨1⟩}).symm (Polynomial.C r)) = _
  rw [hc, projectiveChartRingEquiv_C]
  rfl

private theorem embeddingAway_coordinates :
    (pointChartRing R).symm.toRingHom.comp
        ((embeddingAway R).comp (lineChartRing R).toRingHom) =
      (C : R →+* MvPolynomial {j : pointIndex.{u} // j ≠ ⟨0⟩} R).comp
        (Polynomial.evalRingHom 0) := by
  apply Polynomial.ringHom_ext
  · intro r
    change (pointChartRing R).symm (embeddingAway R (lineChartRing R (Polynomial.C r))) = _
    rw [lineChartRing_C, embeddingAway_mk]
    change (projectiveChartRingEquiv R pointIndex.{u} ⟨0⟩).symm _ = _
    rw [projectiveChartRingEquiv_symm_mk, pointEmbedding_C]
    simp [projectiveDehomogenize]
  · change (pointChartRing R).symm (embeddingAway R (lineChartRing R Polynomial.X)) = _
    rw [lineChartRing_X]
    unfold Away.isLocalizationElem
    rw [embeddingAway_mk]
    change (projectiveChartRingEquiv R pointIndex.{u} ⟨0⟩).symm _ = _
    rw [projectiveChartRingEquiv_symm_mk, map_pow, pointEmbedding_X]
    simp [projectiveDehomogenize]

private def pointOrigin : Spec (.of R) ⟶ projectiveScheme R pointIndex.{u} :=
  Spec.map (CommRingCat.ofHom
    (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩}).toRingHom) ≫
      projectiveChartMap R pointIndex.{u} ⟨0⟩

private theorem graded_square
    (f : homogeneousSubmodule lineIndex.{u} R →+*ᵍ homogeneousSubmodule pointIndex.{u} R)
    (hf : HomogeneousIdeal.irrelevant (homogeneousSubmodule pointIndex.{u} R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule lineIndex.{u} R)).map f)
    (t : MvPolynomial pointIndex.{u} R) (ht : t.IsHomogeneous 1)
    (h : f (X (⟨1⟩ : lineIndex.{u})) = t) :
    Proj.awayι _ t ht Nat.zero_lt_one ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f (by
        rintro _ ⟨n, rfl⟩
        exact ⟨n, by rw [map_pow, h]⟩))) ≫
          Proj.awayι _ _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) Nat.zero_lt_one := by
  subst t
  exact Proj.awayι_comp_map f hf Nat.zero_lt_one _ (isHomogeneous_X R _)

private theorem embedding_square :
    Proj.awayι _ _ (isHomogeneous_X R (⟨0⟩ : pointIndex.{u})) Nat.zero_lt_one ≫
        pointEmbeddingMap R =
      Spec.map (CommRingCat.ofHom (embeddingAway R)) ≫
        Proj.awayι _ _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) Nat.zero_lt_one :=
  graded_square R (pointEmbedding R) (pointEmbedding_irrelevant R)
    (X (⟨0⟩ : pointIndex.{u})) (isHomogeneous_X R _) (by simp [pointEmbedding_X])

private theorem pointOrigin_embedding :
    pointOrigin R ≫ pointEmbeddingMap R =
      projectiveLineSection R (⟨1⟩ : lineIndex.{u}) := by
  have he : (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩}).toRingHom.comp
      ((pointChartRing R).symm.toRingHom.comp (embeddingAway R)) =
    (Polynomial.evalRingHom 0).comp (lineChartRing R).symm.toRingHom := by
    apply RingHom.ext
    intro q
    obtain ⟨q, rfl⟩ := (lineChartRing R).surjective q
    have h := congrArg (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩})
      (DFunLike.congr_fun (embeddingAway_coordinates R) q)
    change (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩})
        ((pointChartRing R).symm (embeddingAway R (lineChartRing R q))) =
      (Polynomial.evalRingHom 0) ((lineChartRing R).symm (lineChartRing R q))
    rw [RingEquiv.symm_apply_apply]
    change (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩})
        ((pointChartRing R).symm (embeddingAway R (lineChartRing R q))) =
      (isEmptyRingEquiv R {j : pointIndex.{u} // j ≠ ⟨0⟩}) (C ((Polynomial.evalRingHom 0) q)) at h
    simpa only [← isEmptyRingEquiv_symm_apply, RingEquiv.apply_symm_apply] using h
  rw [pointOrigin, pointChartMap_eq, Category.assoc, Category.assoc, embedding_square,
    projectiveLineSection, lineChartMap_eq]
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun m => Spec.map (CommRingCat.ofHom m) ≫
    Proj.awayι _ _ (isHomogeneous_X R (⟨1⟩ : lineIndex.{u})) Nat.zero_lt_one) he

private theorem sum_line {A : Type*} [AddCommMonoid A] (f : lineIndex.{u} → A) :
    ∑ j, f j = f ⟨0⟩ + f ⟨1⟩ := by
  rw [Fintype.sum_equiv Equiv.ulift f (fun j : Fin 2 => f ⟨j⟩) (fun _ => rfl),
    Fin.sum_univ_two]

private def translationMatrix (a : R) : Matrix.GeneralLinearGroup lineIndex.{u} R :=
  Matrix.GeneralLinearGroup.transvection (⟨1⟩ : lineIndex.{u}) ⟨0⟩ (by decide) a

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

private def pointScaling (c : Rˣ) : Matrix.GeneralLinearGroup pointIndex.{u} R where
  val := Matrix.diagonal (fun _ => (c : R))
  inv := Matrix.diagonal (fun _ => (↑(c⁻¹) : R))
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

private theorem pointScaling_map (c : Rˣ) :
    projectiveMatrixMap (R := R) (pointScaling R c) = 𝟙 _ := by
  let : IsIso (projectiveToSpec R pointIndex.{u}) := pointBase_isIso R
  apply (cancel_mono (projectiveToSpec R pointIndex.{u})).mp
  simpa only [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id,
    Spec.map_id, Category.comp_id] using
      projectiveMatrixMap_toSpec (R := R) (pointScaling R c)

private theorem embedding_translate (a : R) :
    pointEmbeddingMap R ≫ (projectiveLineTranslationIso a).hom = pointEmbeddingMap R := by
  have he : (pointEmbedding R).comp
      (projectiveMatrixHom (K := R) (translationMatrix R a : Matrix _ _ R)) =
        pointEmbedding R := by
    apply GradedRingHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext
    · intro r
      change pointEmbedding R (projectiveMatrixHom (K := R)
        (translationMatrix R a : Matrix _ _ R) (C r)) = pointEmbedding R (C r)
      rw [projectiveMatrixHom_C, Algebra.algebraMap_self_apply]
    · rintro ⟨j⟩
      change pointEmbedding R (projectiveMatrixHom (K := R)
        (translationMatrix R a : Matrix _ _ R) (X ⟨j⟩)) = pointEmbedding R (X ⟨j⟩)
      fin_cases j <;>
        simp [projectiveMatrixHom_X, translationMatrix,
          Matrix.GeneralLinearGroup.transvection, Matrix.transvection,
          Matrix.single_apply, Matrix.one_apply, map_mul,
          pointEmbedding_C, pointEmbedding_X, sum_line]
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  congr 1

private theorem embedding_scale (c : Rˣ) :
    pointEmbeddingMap R ≫ (projectiveLineScalingIso c).hom = pointEmbeddingMap R := by
  have he : (pointEmbedding R).comp
      (projectiveMatrixHom (K := R) (scalingMatrix R c : Matrix _ _ R)) =
      (projectiveMatrixHom (K := R) (pointScaling R c : Matrix _ _ R)).comp
        (pointEmbedding R) := by
    apply GradedRingHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext
    · intro r
      change pointEmbedding R (projectiveMatrixHom (K := R)
        (scalingMatrix R c : Matrix _ _ R) (C r)) =
          projectiveMatrixHom (K := R) (pointScaling R c : Matrix _ _ R) (pointEmbedding R (C r))
      simp [projectiveMatrixHom_C, pointEmbedding_C]
    · rintro ⟨j⟩
      change pointEmbedding R (projectiveMatrixHom (K := R)
        (scalingMatrix R c : Matrix _ _ R) (X ⟨j⟩)) =
          projectiveMatrixHom (K := R) (pointScaling R c : Matrix _ _ R)
            (pointEmbedding R (X ⟨j⟩))
      fin_cases j <;>
        simp [projectiveMatrixHom_X, scalingMatrix, pointScaling, Matrix.diagonal,
          map_mul, pointEmbedding_C, pointEmbedding_X, sum_line]
      rw [ite_eq_left (Subsingleton.elim _ _)]
      congr 1
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  calc
    Proj.map _ _ = projectiveMatrixMap (R := R) (pointScaling R c) ≫
        pointEmbeddingMap R := by
      rw [projectiveMatrixMap, pointEmbeddingMap, ← Proj.map_comp]
      congr 1
    _ = _ := by rw [pointScaling_map, Category.id_comp]; rfl

/-- Translation fixes the distinguished infinity section over every coefficient ring. -/
theorem projectiveInfinity_translation (a : R) :
    projectiveLineSection R (⟨1⟩ : lineIndex.{u}) ≫
        (projectiveLineTranslationIso a).hom = projectiveLineSection R ⟨1⟩ := by
  rw [← pointOrigin_embedding R, Category.assoc, embedding_translate]

/-- Unit scaling fixes the distinguished infinity section over every coefficient ring. -/
theorem projectiveInfinity_scaling (c : Rˣ) :
    projectiveLineSection R (⟨1⟩ : lineIndex.{u}) ≫
        (projectiveLineScalingIso c).hom = projectiveLineSection R ⟨1⟩ := by
  rw [← pointOrigin_embedding R, Category.assoc, embedding_scale]

/-- The specified affine projective family fixes the same distinguished infinity section. -/
theorem projectiveInfinity_affine (c : Rˣ) (a : R) :
    projectiveLineSection R (⟨1⟩ : lineIndex.{u}) ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom =
      projectiveLineSection R ⟨1⟩ := by
  rw [← Category.assoc, projectiveInfinity_scaling, projectiveInfinity_translation]

end SchubertGeometry.ProjectiveLine
