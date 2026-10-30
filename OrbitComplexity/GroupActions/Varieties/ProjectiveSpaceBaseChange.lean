import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Base change of polynomial projective space

The coefficient homomorphism preserves the homogeneous coordinate charts. On each
chart, its structure square is the affine polynomial base-change square. The chart
cover then gives the projective-space pullback isomorphism.

## Main definitions

* `GroupActions.projectiveCoeffMap`: the projective morphism induced on coefficients.
* `GroupActions.projectiveBaseChange`: the projective-space base-change isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroupActions
variable {R S : Type u} [CommRing R] [CommRing S] (ι : Type u)

private def projectiveCoeffGraded (f : R →+* S) :
    homogeneousSubmodule ι R →+*ᵍ homogeneousSubmodule ι S where
  __ := MvPolynomial.map f
  map_mem hp := hp.map f

private theorem coefficient_irrelevant (f : R →+* S) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule ι S) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).map
        (projectiveCoeffGraded ι f) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_map, projective_irrelevant_eq_span S ι,
    projective_irrelevant_eq_span R ι]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change X i ∈ Ideal.map (MvPolynomial.map f) _
  simpa only [MvPolynomial.map_X] using
    Ideal.mem_map_of_mem (MvPolynomial.map f)
      (Ideal.subset_span (show X i ∈ Set.range (X : ι → MvPolynomial ι R) from ⟨i, rfl⟩))

/-- A coefficient homomorphism induces a morphism of polynomial projective spaces. -/
def projectiveCoeffMap (f : R →+* S) : projectiveScheme S ι ⟶ projectiveScheme R ι :=
  Proj.map (projectiveCoeffGraded ι f) (coefficient_irrelevant ι f)

private theorem projectiveCoeffMap_preimage (f : R →+* S) (j : ι) :
    projectiveCoeffMap ι f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) (X j) =
      Proj.basicOpen (homogeneousSubmodule ι S) (X j) := by
  rw [projectiveCoeffMap, Proj.map_preimage_basicOpen]
  congr 1
  exact MvPolynomial.map_X f j

private theorem polynomial_pullback (σ : Type u) (f : R →+* S) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := σ) f)))
      (Spec.map (CommRingCat.ofHom (C : S →+* MvPolynomial σ S)))
      (Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial σ R)))
      (Spec.map (CommRingCat.ofHom f)) := by
  refine (AffineSpace.isPullback_map (n := σ) (Spec.map (CommRingCat.ofHom f))).of_iso
    (AffineSpace.SpecIso σ (CommRingCat.of S))
    (AffineSpace.SpecIso σ (CommRingCat.of R)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [AffineSpace.map_SpecMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, CommRingCat.hom_ofHom]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (Iso.inv_comp_eq (AffineSpace.SpecIso σ (CommRingCat.of S))).mp
        (AffineSpace.SpecIso_inv_over (n := σ) (CommRingCat.of S))
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (Iso.inv_comp_eq (AffineSpace.SpecIso σ (CommRingCat.of R))).mp
        (AffineSpace.SpecIso_inv_over (n := σ) (CommRingCat.of R))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

private theorem homogeneous_X (A : Type u) [CommRing A] (j : ι) :
    X j ∈ homogeneousSubmodule ι A 1 := isHomogeneous_X A j

private def awayCoeffAux (f : R →+* S) (j : ι) (y : MvPolynomial ι S)
    (hy : projectiveCoeffGraded ι f (X j) = y) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X j) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι S) y :=
  HomogeneousLocalization.map (projectiveCoeffGraded ι f) (by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change y ^ n = projectiveCoeffGraded ι f (X j ^ n)
    rw [map_pow, hy])

private theorem coeff_X (f : R →+* S) (j : ι) :
    projectiveCoeffGraded ι f (X j) = X j := MvPolynomial.map_X f j

private def awayCoeffMap (f : R →+* S) (j : ι) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X j) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι S) (X j) :=
  awayCoeffAux ι f j (X j) (coeff_X ι f j)

private theorem awayCoeffAux_comm (f : R →+* S) (j : ι) (y : MvPolynomial ι S)
    (hy : projectiveCoeffGraded ι f (X j) = y) (hyhom : y ∈ homogeneousSubmodule ι S 1) :
    Proj.awayι _ y hyhom Nat.zero_lt_one ≫ projectiveCoeffMap ι f =
      Spec.map (CommRingCat.ofHom (awayCoeffAux ι f j y hy)) ≫
        Proj.awayι _ (X j) (homogeneous_X ι R j) Nat.zero_lt_one := by
  subst y
  exact Proj.awayι_comp_map (projectiveCoeffGraded ι f) (coefficient_irrelevant ι f)
    Nat.zero_lt_one (X j) (homogeneous_X ι R j)

private theorem awayCoeff_mk (f : R →+* S) (j : ι) (n : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ homogeneousSubmodule ι R (n • 1)) :
    awayCoeffMap ι f j (HomogeneousLocalization.Away.mk _ (homogeneous_X ι R j) n p hp) =
      HomogeneousLocalization.Away.mk _ (homogeneous_X ι S j) n (MvPolynomial.map f p)
        (hp.map f) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayCoeffMap, awayCoeffAux, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  apply Subtype.ext
  change MvPolynomial.map f (X j ^ n) = X j ^ n
  simp only [map_pow, MvPolynomial.map_X]

private theorem chart_natural [Finite ι] (f : R →+* S) (j : ι) :
    (awayCoeffMap ι f j).comp (projectiveChartRingEquiv R ι j).toRingHom =
      (projectiveChartRingEquiv S ι j).toRingHom.comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change awayCoeffMap ι f j (projectiveChartRingEquiv R ι j (C r)) =
      projectiveChartRingEquiv S ι j (MvPolynomial.map f (C r))
    rw [projectiveChartRingEquiv_C, MvPolynomial.map_C, projectiveChartRingEquiv_C]
    have hR : C r ∈ homogeneousSubmodule ι R (0 • 1) := isHomogeneous_C ι r
    have hS : C (f r) ∈ homogeneousSubmodule ι S (0 • 1) := isHomogeneous_C ι (f r)
    change awayCoeffMap ι f j
        (HomogeneousLocalization.Away.mk _ (homogeneous_X ι R j) 0 (C r) hR) =
      HomogeneousLocalization.Away.mk _ (homogeneous_X ι S j) 0 (C (f r)) hS
    simpa only [MvPolynomial.map_C] using awayCoeff_mk ι f j 0 (C r) hR
  · intro i
    change awayCoeffMap ι f j (projectiveChartRingEquiv R ι j (X i)) =
      projectiveChartRingEquiv S ι j (MvPolynomial.map f (X i))
    rw [projectiveChartRingEquiv_X, MvPolynomial.map_X, projectiveChartRingEquiv_X]
    simp only [HomogeneousLocalization.Away.isLocalizationElem, awayCoeff_mk,
      map_pow, MvPolynomial.map_X]

private theorem chartMap_eq [Finite ι] (A : Type u) [CommRing A] (j : ι) :
    projectiveChartMap A ι j =
      Spec.map (projectiveChartRingEquiv A ι j).toCommRingCatIso.inv ≫
        Proj.awayι _ _ (homogeneous_X ι A j) Nat.zero_lt_one := by
  simp only [projectiveChartMap, projectiveChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Category.assoc]
  rfl

/-- On a standard chart, the coefficient morphism is polynomial coefficient base change. -/
theorem projectiveCoeffMap_chart [Finite ι] (f : R →+* S) (j : ι) :
    projectiveChartMap S ι j ≫ projectiveCoeffMap ι f =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫ projectiveChartMap R ι j := by
  have hn : (projectiveChartRingEquiv S ι j).symm.toRingHom.comp (awayCoeffMap ι f j) =
      (MvPolynomial.map f).comp (projectiveChartRingEquiv R ι j).symm.toRingHom := by
    apply RingHom.ext
    intro z
    obtain ⟨p, rfl⟩ := (projectiveChartRingEquiv R ι j).surjective z
    change (projectiveChartRingEquiv S ι j).symm
      (awayCoeffMap ι f j (projectiveChartRingEquiv R ι j p)) = _
    have ht := DFunLike.congr_fun (chart_natural ι f j) p
    change awayCoeffMap ι f j (projectiveChartRingEquiv R ι j p) =
      projectiveChartRingEquiv S ι j (MvPolynomial.map f p) at ht
    rw [ht]
    change (projectiveChartRingEquiv S ι j).symm
      (projectiveChartRingEquiv S ι j (MvPolynomial.map f p)) =
        MvPolynomial.map f ((projectiveChartRingEquiv R ι j).symm
          (projectiveChartRingEquiv R ι j p))
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  have hs :
      Spec.map (projectiveChartRingEquiv S ι j).toCommRingCatIso.inv ≫
          Spec.map (CommRingCat.ofHom (awayCoeffMap ι f j)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫
          Spec.map (projectiveChartRingEquiv R ι j).toCommRingCatIso.inv := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact congrArg (fun g => CommRingCat.ofHom g) hn
  rw [chartMap_eq, chartMap_eq, Category.assoc,
    awayCoeffAux_comm ι f j (X j) (coeff_X ι f j) (homogeneous_X ι S j)]
  simpa only [awayCoeffMap, Category.assoc] using congrArg
    (fun z => z ≫ Proj.awayι _ (X j) (homogeneous_X ι R j) Nat.zero_lt_one) hs

private theorem chart_pullback [Finite ι] (f : R →+* S) (j : ι) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := {i : ι // i ≠ j}) f)))
      (projectiveChartMap S ι j) (projectiveChartMap R ι j) (projectiveCoeffMap ι f) := by
  apply IsOpenImmersion.isPullback
  · exact projectiveCoeffMap_chart ι f j
  · rw [projectiveChartMap_range, projectiveChartMap_range, projectiveCoeffMap_preimage]

private theorem projective_pullback [Finite ι] (f : R →+* S) :
    IsPullback (projectiveCoeffMap ι f) (projectiveToSpec S ι)
      (projectiveToSpec R ι) (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (projectiveChartCover R ι)
  intro j
  change ι at j
  let h := (chart_pullback ι f j).flip
  refine (polynomial_pullback {i : ι // i ≠ j} f).of_iso
    h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫ 𝟙 _ =
      h.isoPullback.hom ≫ pullback.snd _ _
    rw [Category.comp_id]
    exact h.isoPullback_hom_snd.symm
  · change Spec.map (CommRingCat.ofHom (C : S →+* MvPolynomial {i : ι // i ≠ j} S)) ≫
        𝟙 _ = h.isoPullback.hom ≫ pullback.fst _ _ ≫ projectiveToSpec S ι
    rw [Category.comp_id, h.isoPullback_hom_fst_assoc]
    exact (projectiveChartMap_toSpec S ι j).symm
  · change Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial {i : ι // i ≠ j} R)) ≫
        𝟙 _ = 𝟙 _ ≫ projectiveChartMap R ι j ≫ projectiveToSpec R ι
    rw [Category.comp_id, Category.id_comp]
    exact (projectiveChartMap_toSpec R ι j).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Finite-coordinate projective space commutes with coefficient base change. -/
def projectiveBaseChange [Finite ι] (f : R →+* S) :
    projectiveScheme S ι ≅
      pullback (Spec.map (CommRingCat.ofHom f)) (projectiveToSpec R ι) :=
  (projective_pullback ι f).flip.isoPullback

/-- The first base-change projection is the structure morphism over the new ring. -/
theorem projectiveBaseChange_fst [Finite ι] (f : R →+* S) :
    (projectiveBaseChange ι f).hom ≫ pullback.fst _ _ = projectiveToSpec S ι :=
  (projective_pullback ι f).flip.isoPullback_hom_fst

/-- The second base-change projection is the projective coefficient morphism. -/
theorem projectiveBaseChange_snd [Finite ι] (f : R →+* S) :
    (projectiveBaseChange ι f).hom ≫ pullback.snd _ _ = projectiveCoeffMap ι f :=
  (projective_pullback ι f).flip.isoPullback_hom_snd

end GroupActions
