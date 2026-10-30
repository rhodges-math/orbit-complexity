import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsInverse
import OrbitComplexity.GroupActions.Varieties.Morphisms
import Batteries.Tactic.Lint

/-! # Rational points from homogeneous vectors

Homogeneous polynomial evaluation associates a rational point of projective space to each
nonzero vector. Its homogeneous vanishing ideal, invariance under nonzero scalar
multiplication, and affine chart coordinates describe this construction over every field.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
universe u
variable {K ι : Type u} [Field K] [Finite ι]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem residue_sections_unique (X : Scheme.{u})
    (a : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (d e : X.residueField x ⟶ CommRingCat.of K)
    (hd : (Spec.map d ≫ X.fromSpecResidueField x) ≫ a = 𝟙 _)
    (he : (Spec.map e ≫ X.fromSpecResidueField x) ≫ a = 𝟙 _) : d = e := by
  let b := Spec.preimage (X.fromSpecResidueField x ≫ a)
  have hd' : b ≫ d = 𝟙 _ := by
    have hh : Spec.map d ≫ (X.fromSpecResidueField x ≫ a) = 𝟙 _ := by
      simpa only [Category.assoc] using hd
    simpa only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] using
      congrArg Spec.preimage hh
  have he' : b ≫ e = 𝟙 _ := by
    have hh : Spec.map e ≫ (X.fromSpecResidueField x ≫ a) = 𝟙 _ := by
      simpa only [Category.assoc] using he
    simpa only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] using
      congrArg Spec.preimage hh
  have : Mono d := ConcreteCategory.mono_of_injective d d.hom.injective
  have hdb : d ≫ b = 𝟙 _ := by
    apply (cancel_mono d).mp
    rw [Category.assoc, hd', Category.comp_id, Category.id_comp]
  calc
    d = d ≫ (b ≫ e) := by rw [he', Category.comp_id]
    _ = e := by rw [← Category.assoc, hdb, Category.id_comp]

private theorem rational_point_ext (X : GroupActions.Variety K)
    (p q : X.points) (h : X.pointMap p = X.pointMap q) : p = q := by
  change p.val (IsLocalRing.closedPoint K) = q.val (IsLocalRing.closedPoint K) at h
  apply Subtype.ext
  apply (Scheme.SpecToEquivOfField K X.scheme).injective
  change (⟨p.val (IsLocalRing.closedPoint K),
      X.scheme.descResidueField (Scheme.stalkClosedPointTo p.val)⟩ :
        Σ x, X.scheme.residueField x ⟶ CommRingCat.of K) =
    ⟨q.val (IsLocalRing.closedPoint K),
      X.scheme.descResidueField (Scheme.stalkClosedPointTo q.val)⟩
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨h, ?_⟩
  apply residue_sections_unique X.scheme X.toSpec (p.val (IsLocalRing.closedPoint K))
  · rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    exact p.property
  · change (Spec.map ((X.scheme.residueFieldCongr h).hom ≫
        X.scheme.descResidueField (Scheme.stalkClosedPointTo q.val)) ≫
        X.scheme.fromSpecResidueField (p.val (IsLocalRing.closedPoint K))) ≫ X.toSpec = _
    simp only [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField_assoc]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ X.toSpec)
        (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X.scheme q.val)).trans
          q.property

private def globalEval (v : ι → K) :
    MvPolynomial ι K →+* Γ(Spec (CommRingCat.of K), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp (eval v)

omit [Finite ι] in
private theorem eval_irrelevant (v : ι → K) (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι K)).toIdeal.map (globalEval v) =
      ⊤ := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  have hx : X j ∈ (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι K)).toIdeal := by
    rw [GroupActions.projective_irrelevant_eq_span]
    exact Ideal.subset_span ⟨j, rfl⟩
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (globalEval v) hx)
  change IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (eval v (X j)))
  rw [eval_X]
  exact (isUnit_iff_ne_zero.mpr hj).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

private def vectorMorphism (v : ι → K) (hv : v ≠ 0) :
    Spec (CommRingCat.of K) ⟶ GroupActions.projectiveScheme K ι :=
  Proj.fromOfGlobalSections (homogeneousSubmodule ι K) (globalEval v) (eval_irrelevant v hv)

omit [Finite ι] in
private theorem vectorMorphism_base (v : ι → K) (hv : v ≠ 0) :
    vectorMorphism v hv ≫ GroupActions.projectiveToSpec K ι = 𝟙 _ := by
  rw [GroupActions.projectiveToSpec, ← Category.assoc]
  change (Proj.fromOfGlobalSections (homogeneousSubmodule ι K) (globalEval v)
      (eval_irrelevant v hv) ≫ Proj.toSpecZero (homogeneousSubmodule ι K)) ≫ _ = _
  rw [Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp]
  have he : (GroupActions.projectiveZeroIso K ι).toCommRingCatIso.hom ≫
      CommRingCat.ofHom ((globalEval v).comp
        (algebraMap (homogeneousSubmodule ι K 0) (MvPolynomial ι K))) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    ext r
    change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (eval v (C r)) = _
    rw [eval_C]
  rw [he]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

/-- The rational projective point defined by a nonzero homogeneous coordinate vector. -/
def projectiveVectorPoint (v : ι → K) (hv : v ≠ 0) :
    (GroupActions.projectiveVariety K ι).points :=
  ⟨vectorMorphism v hv, vectorMorphism_base v hv⟩

omit [Finite ι] in
private theorem homogeneous_eval_smul (v : ι → K) (t : K)
    (p : MvPolynomial ι K) (n : ℕ) (hp : p.IsHomogeneous n) :
    eval (t • v) p = t ^ n * eval v p := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

omit [Finite ι] in
private theorem constant_mem
    (x : ProjectiveSpectrum (homogeneousSubmodule ι K)) (r : K) :
    C r ∈ x.asHomogeneousIdeal ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    exact x.isPrime.ne_top (x.asHomogeneousIdeal.toIdeal.eq_top_of_isUnit_mem h
      ((isUnit_iff_ne_zero.mpr hr).map (C : K →+* MvPolynomial ι K)))
  · rintro rfl
    rw [map_zero]
    exact zero_mem x.asHomogeneousIdeal

/-- A projective vector belongs to a homogeneous basic open exactly when that polynomial
does not vanish on the vector. -/
theorem projectiveVectorPoint_basicOpen (v : ι → K) (hv : v ≠ 0)
    (n : ℕ) (hn : 0 < n) (p : MvPolynomial ι K) (hp : p.IsHomogeneous n) :
    (GroupActions.projectiveVariety K ι).pointMap (projectiveVectorPoint v hv) ∈
        Proj.basicOpen (homogeneousSubmodule ι K) p ↔ eval v p ≠ 0 := by
  change IsLocalRing.closedPoint K ∈
    (vectorMorphism v hv) ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι K) p ↔ _
  unfold vectorMorphism
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hp]
  change IsLocalRing.closedPoint K ∈ (Spec (CommRingCat.of K)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (eval v p)) ↔ _
  rw [basicOpen_eq_of_affine]
  change eval v p ∉ IsLocalRing.maximalIdeal K ↔ eval v p ≠ 0
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- A positive-degree homogeneous polynomial vanishes exactly when its vector evaluation is zero. -/
theorem projectiveVectorPoint_mem (v : ι → K) (hv : v ≠ 0)
    (n : ℕ) (hn : 0 < n) (p : MvPolynomial ι K) (hp : p.IsHomogeneous n) :
    p ∈ ((GroupActions.projectiveVariety K ι).pointMap
      (projectiveVectorPoint v hv)).asHomogeneousIdeal ↔ eval v p = 0 := by
  have h := not_congr (projectiveVectorPoint_basicOpen v hv n hn p hp)
  change (¬ (p ∉ ((GroupActions.projectiveVariety K ι).pointMap
    (projectiveVectorPoint v hv)).asHomogeneousIdeal)) ↔ ¬ (eval v p ≠ 0) at h
  simpa only [not_not] using h

omit [Finite ι] in
private theorem positive_parts_ext
    (x y : ProjectiveSpectrum (homogeneousSubmodule ι K))
    (h : ∀ (n : ℕ), 0 < n → ∀ (p : MvPolynomial ι K), p.IsHomogeneous n →
      (p ∈ x.asHomogeneousIdeal ↔ p ∈ y.asHomogeneousIdeal)) : x = y := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
    have he : p = C (p.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp.totalDegree_le)
    rw [he, constant_mem, constant_mem]
  | succ n => exact h (n + 1) (Nat.succ_pos n) p hp

/-- Multiplying homogeneous coordinates by a unit preserves the projective point. -/
theorem projectiveVectorPoint_scale (v : ι → K) (hv : v ≠ 0) (t : Kˣ) :
    projectiveVectorPoint ((t : K) • v) (smul_ne_zero t.ne_zero hv) =
      projectiveVectorPoint v hv := by
  apply rational_point_ext
  apply positive_parts_ext
  intro n hn p hp
  rw [projectiveVectorPoint_mem _ _ n hn p hp, projectiveVectorPoint_mem _ _ n hn p hp,
    homogeneous_eval_smul v (t : K) p n hp]
  simp only [mul_eq_zero, pow_ne_zero n t.ne_zero, false_or]
omit [Finite ι] in
private theorem variable_mem (j : ι) : X j ∈ homogeneousSubmodule ι K 1 :=
  isHomogeneous_X K j
private def completeCoordinates (j : ι) (x : {i : ι // i ≠ j} → K) : ι → K := by
  classical
  exact fun i => if h : i = j then 1 else x ⟨i, h⟩

omit [Finite ι] in
private theorem eval_dehomogenize (j : ι) (x : {i : ι // i ≠ j} → K)
    (p : MvPolynomial ι K) :
    eval x (GroupActions.projectiveDehomogenize K ι j p) =
      eval (completeCoordinates j x) p := by
  classical
  have he : (eval x).comp (GroupActions.projectiveDehomogenize K ι j) =
      eval (completeCoordinates j x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [GroupActions.projectiveDehomogenize]
    · intro i
      by_cases h : i = j <;>
        simp [GroupActions.projectiveDehomogenize, completeCoordinates, h]
  exact DFunLike.congr_fun he p

private theorem chart_map_eq (j : ι) : GroupActions.projectiveChartMap K ι j =
    Spec.map (GroupActions.projectiveChartRingEquiv K ι j).toCommRingCatIso.inv ≫
      Proj.awayι _ _ (variable_mem j) Nat.zero_lt_one := by
  simp only [GroupActions.projectiveChartMap, GroupActions.projectiveChartIso,
    Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Category.assoc]
  rfl

private theorem chartPoint_basicOpen (j : ι) (x : {i : ι // i ≠ j} → K)
    (n : ℕ) (hn : 0 < n) (p : MvPolynomial ι K) (hp : p ∈ homogeneousSubmodule ι K n) :
    (GroupActions.projectiveVariety K ι).pointMap
        (GroupActions.Variety.mapPoints (GroupActions.projectiveChartMorphism K ι j)
          ((GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm x)) ∈
      Proj.basicOpen (homogeneousSubmodule ι K) p ↔
        eval (completeCoordinates j x) p ≠ 0 := by
  let a := (GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm x
  change (a.val ≫ GroupActions.projectiveChartMap K ι j) (IsLocalRing.closedPoint K) ∈ _ ↔ _
  rw [chart_map_eq]
  change (Spec.map (GroupActions.projectiveChartRingEquiv K ι j).toCommRingCatIso.inv)
      (a.val (IsLocalRing.closedPoint K)) ∈
    (Proj.awayι _ _ (variable_mem j) Nat.zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule ι K) p ↔ _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := homogeneousSubmodule ι K)
    (variable_mem j) Nat.zero_lt_one hp hn]
  have ha := GroupActions.affinePointsEquiv_prime (MvPolynomial.aeval x)
  change a.val (IsLocalRing.closedPoint K) = _ at ha
  rw [ha]
  change eval x ((GroupActions.projectiveChartRingEquiv K ι j).symm
    (Away.isLocalizationElem (variable_mem j) hp)) ≠ 0 ↔ _
  change eval x ((GroupActions.projectiveChartRingEquiv K ι j).symm
    (Away.mk _ (variable_mem j) n (p ^ 1) _)) ≠ 0 ↔ _
  simp only [pow_one]
  rw [GroupActions.projectiveChartRingEquiv_symm_mk, eval_dehomogenize]

/-- In a coordinate chart, a homogeneous vector has the ratios to its nonzero coordinate. -/
theorem projectiveVectorPoint_chart (v : ι → K) (hv : v ≠ 0) (j : ι) (hj : v j ≠ 0) :
    projectiveVectorPoint v hv =
      GroupActions.Variety.mapPoints (GroupActions.projectiveChartMorphism K ι j)
        ((GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm
          (fun i => v i.val / v j)) := by
  apply rational_point_ext
  apply positive_parts_ext
  intro n hn p hp
  rw [projectiveVectorPoint_mem v hv n hn p hp]
  let x : {i : ι // i ≠ j} → K := fun i => v i.val / v j
  let q := GroupActions.Variety.mapPoints (GroupActions.projectiveChartMorphism K ι j)
    ((GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm x)
  change eval v p = 0 ↔
    p ∈ ((GroupActions.projectiveVariety K ι).pointMap q).asHomogeneousIdeal
  have hz : p ∈ ((GroupActions.projectiveVariety K ι).pointMap q).asHomogeneousIdeal ↔
      eval (completeCoordinates j x) p = 0 := by
    have h := not_congr (chartPoint_basicOpen j x n hn p hp)
    change (¬ (p ∉ ((GroupActions.projectiveVariety K ι).pointMap q).asHomogeneousIdeal)) ↔
      ¬ (eval (completeCoordinates j x) p ≠ 0) at h
    simpa only [not_not] using h
  rw [hz]
  have he : completeCoordinates j x = (v j)⁻¹ • v := by
    classical
    funext i
    by_cases hi : i = j
    · subst i
      simp [completeCoordinates, Pi.smul_apply, smul_eq_mul, hj]
    · simp [completeCoordinates, hi, x, div_eq_mul_inv, mul_comm]
  rw [he, homogeneous_eval_smul v (v j)⁻¹ p n hp]
  simp only [mul_eq_zero, pow_ne_zero n (inv_ne_zero hj), false_or]
end GroupActions
