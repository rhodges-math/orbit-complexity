import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected

/-! # Specialization of affine projective families at rational coefficients -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions Topology
open CartesianMonoidalCategory MonoidalCategory
universe u
variable {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
  [IsDomain R] [Algebra.FiniteType K R]

private abbrev line := projectiveVariety K (ULift.{u} (Fin 2))
private abbrev coefficients := affineVariety K R

private instance coefficientsIntegral : IsIntegral (coefficients (K := K) (R := R)).scheme := by
  change IsIntegral (Spec (CommRingCat.of R))
  infer_instance

private instance lineIntegral : IsIntegral (line (K := K)).scheme := by
  change IsIntegral (projectiveScheme K (ULift.{u} (Fin 2)))
  infer_instance

private def polynomialChart : (affineVariety K (Polynomial K)).toOver ⟶ (line (K := K)).toOver :=
  Over.homMk (projectiveLinePolynomialChart K ⟨0⟩) (projectiveLinePolynomialChart_base K ⟨0⟩)

private def parameterSection (a : R →ₐ[K] K) :
    projectiveScheme K (ULift.{u} (Fin 2)) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap K R)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) :=
  Limits.pullback.lift
    (projectiveToSpec K (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom a.toRingHom))
    (𝟙 _) (by
      rw [Category.assoc, ← Spec.map_comp]
      have he : CommRingCat.ofHom (algebraMap K R) ≫ CommRingCat.ofHom a.toRingHom =
          𝟙 (CommRingCat.of K) := by ext k; exact a.commutes k
      rw [he, Spec.map_id, Category.comp_id, Category.id_comp])

omit [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] in
private theorem section_chart (a : R →ₐ[K] K) :
    projectiveLinePolynomialChart K ⟨0⟩ ≫ parameterSection a =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom a.toRingHom)) ≫
        projectiveLinePolynomialChart R ⟨0⟩ ≫
          (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom := by
  rw [projectiveBaseChange_polynomial_chart]
  apply Limits.pullback.hom_ext
  · simp only [parameterSection, Category.assoc, Limits.pullback.lift_fst]
    rw [← Category.assoc, projectiveLinePolynomialChart_base,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change Polynomial.C (a r) = Polynomial.map a.toRingHom (Polynomial.C r)
    simp
  · simp only [parameterSection, Category.assoc, Limits.pullback.lift_snd,
      Category.comp_id]
    rw [← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K R)) ≫
        CommRingCat.ofHom (Polynomial.mapRingHom a.toRingHom) =
          𝟙 (CommRingCat.of (Polynomial K)) := by
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro k
        simp
      · simp
    rw [he, Spec.map_id, Category.id_comp]

omit [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] in
private theorem polynomial_specialization (a : R →ₐ[K] K) (c : Rˣ) (m : R) :
    (Polynomial.mapRingHom a.toRingHom).comp
        ((Polynomial.algEquivCMulXAddC (c : R) m).toRingHom.comp
          (Polynomial.mapRingHom (algebraMap K R))) =
      (Polynomial.algEquivCMulXAddC ((Units.map a.toMonoidHom c : Kˣ) : K) (a m)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro k
    change Polynomial.map a.toRingHom
        ((Polynomial.aeval (Polynomial.C (c : R) * Polynomial.X + Polynomial.C m))
          (Polynomial.map (algebraMap K R) (Polynomial.C k))) =
      (Polynomial.aeval (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (a m)))
        (Polynomial.C k)
    simp
  · change Polynomial.map a.toRingHom
        ((Polynomial.aeval (Polynomial.C (c : R) * Polynomial.X + Polynomial.C m))
          (Polynomial.map (algebraMap K R) Polynomial.X)) =
      (Polynomial.aeval (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (a m)))
        Polynomial.X
    simp

omit [IsAlgClosed K] [IsDomain R] [Algebra.FiniteType K R] in
private theorem specialized_chart (a : R →ₐ[K] K) (c : Rˣ) (m : R) :
    projectiveLinePolynomialChart K ⟨0⟩ ≫
        parameterSection a ≫
        (projectiveAffineFamily (algebraMap K R) c m).left =
      projectiveLinePolynomialChart K ⟨0⟩ ≫
        (projectiveLineScalingIso (Units.map a.toMonoidHom c)).hom ≫
        (projectiveLineTranslationIso (a m)).hom := by
  rw [← Category.assoc, section_chart, Category.assoc, Category.assoc,
    projectiveAffineFamily_chart, ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom
      ((Polynomial.algEquivCMulXAddC (c : R) m).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap K R))) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom a.toRingHom) =
        CommRingCat.ofHom
          (Polynomial.algEquivCMulXAddC
            ((Units.map a.toMonoidHom c : Kˣ) : K) (a m)).toRingHom := by
    apply CommRingCat.hom_ext
    exact polynomial_specialization a c m
  rw [he, ← reassoc_of% (projectiveLineScaling_chart (Units.map a.toMonoidHom c)),
    ← projectiveLineTranslation_chart (a m), ← Category.assoc, ← Spec.map_comp]
  have hp : CommRingCat.ofHom
      (Polynomial.algEquivCMulXAddC ((Units.map a.toMonoidHom c : Kˣ) : K) (a m)).toRingHom =
        CommRingCat.ofHom (Polynomial.algEquivAevalXAddC (a m)).toRingHom ≫
          CommRingCat.ofHom
            (Polynomial.algEquivCMulXAddC ((Units.map a.toMonoidHom c : Kˣ) : K) 0).toRingHom := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro k
      change (Polynomial.aeval
          (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (a m))) (Polynomial.C k) =
        (Polynomial.aeval (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (0 : K)))
          ((Polynomial.aeval (Polynomial.X + Polynomial.C (a m))) (Polynomial.C k))
      simp
    · change (Polynomial.aeval
          (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (a m))) Polynomial.X =
        (Polynomial.aeval (Polynomial.C (a (c : R)) * Polynomial.X + Polynomial.C (0 : K)))
          ((Polynomial.aeval (Polynomial.X + Polynomial.C (a m))) Polynomial.X)
      simp
  exact congrArg (fun h => Spec.map h ≫ projectiveLinePolynomialChart K ⟨0⟩) hp

private theorem eq_on_chart
    (f g : projectiveScheme K (ULift.{u} (Fin 2)) ⟶
      projectiveScheme K (ULift.{u} (Fin 2)))
    (hf : f ≫ projectiveToSpec K (ULift.{u} (Fin 2)) =
      projectiveToSpec K (ULift.{u} (Fin 2)))
    (hg : g ≫ projectiveToSpec K (ULift.{u} (Fin 2)) =
      projectiveToSpec K (ULift.{u} (Fin 2)))
    (h : projectiveLinePolynomialChart K ⟨0⟩ ≫ f =
      projectiveLinePolynomialChart K ⟨0⟩ ≫ g) : f = g := by
  have : LocallyOfFiniteType (f ≫ projectiveToSpec K (ULift.{u} (Fin 2))) := by
    rw [hf]
    infer_instance
  have hne : (Set.range (projectiveLinePolynomialChart K (⟨0⟩ : ULift.{u} (Fin 2)))).Nonempty :=
    ⟨_, (affineVariety K (Polynomial K)).pointMap
      ((affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval (0 : K))), rfl⟩
  apply AlgebraicGeometry.ext_of_apply_eq (projectiveToSpec K (ULift.{u} (Fin 2)))
    (Set.range (projectiveLinePolynomialChart K ⟨0⟩))
    (projectiveLinePolynomialChart K ⟨0⟩).isOpenEmbedding.2.isLocallyClosed
    ((projectiveLinePolynomialChart K ⟨0⟩).isOpenEmbedding.2.dense hne)
  · rintro x ⟨z, rfl⟩ _
    exact congrArg (fun k => k z) h
  · exact hf.trans hg.symm

omit [IsDomain R] [Algebra.FiniteType K R] in
private theorem family_specialization (a : R →ₐ[K] K) (c : Rˣ) (m : R) :
    parameterSection a ≫ (projectiveAffineFamily (algebraMap K R) c m).left =
      (projectiveLineScalingIso (Units.map a.toMonoidHom c)).hom ≫
        (projectiveLineTranslationIso (a m)).hom := by
  have he : CommRingCat.ofHom (algebraMap K R) ≫ CommRingCat.ofHom a.toRingHom =
      𝟙 (CommRingCat.of K) := by ext k; exact a.commutes k
  apply eq_on_chart
  · have hw := (projectiveAffineFamily (algebraMap K R) c m).w
    change (projectiveAffineFamily (algebraMap K R) c m).left ≫
      projectiveToSpec K (ULift.{u} (Fin 2)) =
        Limits.pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) at hw
    rw [Category.assoc, hw]
    change parameterSection a ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K R)) = _
    rw [← Category.assoc]
    change (Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _) ≫ _ = _
    rw [Limits.pullback.lift_fst, Category.assoc, ← Spec.map_comp,
      he, Spec.map_id, Category.comp_id]
  · rw [Category.assoc, projectiveLineTranslation_base, projectiveLineScaling_base]
  · exact specialized_chart a c m

private theorem pointSection_parameter (a : R →ₐ[K] K) :
    (Variety.pointSection (coefficients (K := K) (R := R)) (line (K := K))
      ((affineVarietyPointsEquiv K R).symm a)).left = parameterSection a := by
  apply Limits.pullback.hom_ext
  · have h : Variety.pointSection (coefficients (K := K) (R := R)) (line (K := K))
        ((affineVarietyPointsEquiv K R).symm a) ≫
        fst (coefficients (K := K) (R := R)).toOver (line (K := K)).toOver =
      toUnit (line (K := K)).toOver ≫ (coefficients (K := K) (R := R)).pointsEquivOverHom
        ((affineVarietyPointsEquiv K R).symm a) := lift_fst _ _
    have hu : (toUnit (line (K := K)).toOver).left =
        projectiveToSpec K (ULift.{u} (Fin 2)) := Over.toUnit_left
    have hl := congrArg Over.Hom.left h
    change _ = (toUnit (line (K := K)).toOver).left ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) at hl
    exact hl.trans ((congrArg (fun q => q ≫ Spec.map (CommRingCat.ofHom a.toRingHom)) hu).trans
      (Limits.pullback.lift_fst _ _ _).symm)
  · have h := Variety.pointSection_snd (coefficients (K := K) (R := R)) (line (K := K))
      ((affineVarietyPointsEquiv K R).symm a)
    exact (congrArg Over.Hom.left h).trans (Limits.pullback.lift_snd _ _ _).symm

private theorem section_specialization (a : R →ₐ[K] K) (c : Rˣ) (m : R) :
    Variety.pointSection (coefficients (K := K) (R := R)) (line (K := K))
        ((affineVarietyPointsEquiv K R).symm a) ≫
        projectiveAffineFamily (algebraMap K R) c m =
      Over.homMk ((projectiveLineScalingIso (Units.map a.toMonoidHom c)).hom ≫
        (projectiveLineTranslationIso (a m)).hom) (by
          change ((projectiveLineScalingIso (Units.map a.toMonoidHom c)).hom ≫
            (projectiveLineTranslationIso (a m)).hom) ≫
              projectiveToSpec K (ULift.{u} (Fin 2)) =
                projectiveToSpec K (ULift.{u} (Fin 2))
          rw [Category.assoc, projectiveLineTranslation_base, projectiveLineScaling_base]) := by
  apply Over.OverMorphism.ext
  exact (congrArg (fun q => q ≫ (projectiveAffineFamily (algebraMap K R) c m).left)
    (pointSection_parameter a)).trans (family_specialization a c m)

private theorem translation_scaling (c : Kˣ) (m : K) :
    (projectiveLineTranslationIso m).hom ≫ (projectiveLineScalingIso c).hom =
      (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso ((c : K) * m)).hom := by
  apply eq_on_chart
  · rw [Category.assoc, projectiveLineScaling_base, projectiveLineTranslation_base]
  · rw [Category.assoc, projectiveLineTranslation_base, projectiveLineScaling_base]
  · rw [← reassoc_of% (projectiveLineTranslation_chart m),
      ← projectiveLineScaling_chart c,
      ← reassoc_of% (projectiveLineScaling_chart c),
      ← projectiveLineTranslation_chart ((c : K) * m),
      ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : K) 0).toRingHom ≫
        CommRingCat.ofHom (Polynomial.algEquivAevalXAddC m).toRingHom =
      CommRingCat.ofHom (Polynomial.algEquivAevalXAddC ((c : K) * m)).toRingHom ≫
        CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : K) 0).toRingHom := by
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro k
        simp
      · simp [mul_add]
    rw [he]

/-- A rational coefficient point specializes the affine family to its two fixed factors. -/
theorem projectiveAffineFamily_specialize (a : R →ₐ[K] K) (c : Rˣ) (m : R) :
    (Variety.pointSection (affineVariety K R)
        (projectiveVariety K (ULift.{u} (Fin 2)))
        ((affineVarietyPointsEquiv K R).symm a)).left ≫
        (projectiveAffineFamily (algebraMap K R) c ((c : R) * m)).left =
      (projectiveLineTranslationIso (a m)).hom ≫
        (projectiveLineScalingIso (Units.map a.toMonoidHom c)).hom := by
  have h := family_specialization a c ((c : R) * m)
  have he : a ((c : R) * m) = (Units.map a.toMonoidHom c : K) * a m := map_mul a _ _
  rw [he] at h
  exact (congrArg (fun q => q ≫
      (projectiveAffineFamily (algebraMap K R) c ((c : R) * m)).left)
        (pointSection_parameter a)).trans
    (h.trans (translation_scaling (Units.map a.toMonoidHom c) (a m)).symm)

end SchubertGeometry
