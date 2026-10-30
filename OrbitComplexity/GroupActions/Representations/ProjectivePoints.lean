import OrbitComplexity.GroupActions.Representations.ProjectiveVectors
import OrbitComplexity.GroupActions.Varieties.OpenCoverPoints
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Projective lines and rational projective points

The scalar classes of nonzero vectors are in bijection with rational points of projective
space. Standard affine charts prove surjectivity over every field.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
variable {K ι : Type u} [Field K] [Finite ι]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projectiveVectorPoint_eq_iff (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    projectiveVectorPoint v hv = projectiveVectorPoint w hw ↔ ∃ t : Kˣ, t • w = v := by
  constructor
  · intro he
    obtain ⟨j, hwj⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.mp hw
    have hvj : v j ≠ 0 := by
      have hz : v j = 0 ↔ w j = 0 := by
        have h1 := projectiveVectorPoint_mem v hv 1 Nat.zero_lt_one (X j)
          (isHomogeneous_X K j)
        have h2 := projectiveVectorPoint_mem w hw 1 Nat.zero_lt_one (X j)
          (isHomogeneous_X K j)
        rw [he] at h1
        simpa only [eval_X] using h1.symm.trans h2
      exact fun h => hwj (hz.mp h)
    refine ⟨Units.mk0 (v j / w j) (div_ne_zero hvj hwj), ?_⟩
    funext i
    have hrel : w j * v i - w i * v j = 0 := by
      let p : MvPolynomial ι K := C (w j) * X i - C (w i) * X j
      have hp : p.IsHomogeneous 1 := by
        have h1 := (isHomogeneous_C ι (w j)).mul (isHomogeneous_X K i)
        have h2 := (isHomogeneous_C ι (w i)).mul (isHomogeneous_X K j)
        simpa only [p, zero_add] using h1.sub h2
      have hw0 : eval w p = 0 := by
        simp only [p, map_sub, map_mul, eval_C, eval_X]
        ring
      have hm : p ∈ ((GroupActions.projectiveVariety K ι).pointMap
          (projectiveVectorPoint v hv)).asHomogeneousIdeal := by
        rw [he, projectiveVectorPoint_mem w hw 1 Nat.zero_lt_one p hp]
        exact hw0
      have hv0 := (projectiveVectorPoint_mem v hv 1 Nat.zero_lt_one p hp).mp hm
      simpa only [p, map_sub, map_mul, eval_C, eval_X] using hv0
    change (v j / w j) * w i = v i
    apply (mul_right_cancel₀ hwj)
    calc
      (v j / w j * w i) * w j = (v j / w j * w j) * w i := by ring
      _ = v j * w i := by rw [div_mul_cancel₀ _ hwj]
      _ = v i * w j := by simpa only [mul_comm] using (sub_eq_zero.mp hrel).symm
  · rintro ⟨t, ht⟩
    change (t : K) • w = v at ht
    cases ht
    exact projectiveVectorPoint_scale w hw t

private def projectivePointMap :
    Projectivization K (ι → K) → (GroupActions.projectiveVariety K ι).points :=
  Projectivization.lift (fun v => projectiveVectorPoint v.val v.property) (by
    intro a b t ht
    change a.val = t • b.val at ht
    have htn : t ≠ 0 := by
      intro h0
      apply a.property
      simpa only [h0, zero_smul] using ht
    apply (projectiveVectorPoint_eq_iff a.val b.val a.property b.property).mpr
    exact ⟨Units.mk0 t htn, ht.symm⟩)

private theorem projectivePointMap_injective :
    Function.Injective (projectivePointMap (K := K) (ι := ι)) := by
  intro p q he
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      apply (Projectivization.mk_eq_mk_iff K v w hv hw).mpr
      change projectiveVectorPoint v hv = projectiveVectorPoint w hw at he
      exact (projectiveVectorPoint_eq_iff v w hv hw).mp he
private theorem projectivePointMap_surjective :
    Function.Surjective (projectivePointMap (K := K) (ι := ι)) := by
  classical
  intro q
  obtain ⟨j, z, hz⟩ := GroupActions.point_factors_openCover
    (GroupActions.projectiveChartCover K ι) q.val
  change ι at j
  change Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of
    (MvPolynomial {i : ι // i ≠ j} K)) at z
  change z ≫ GroupActions.projectiveChartMap K ι j = q.val at hz
  have hb : z ≫ (GroupActions.affineSpaceVariety K {i : ι // i ≠ j}).toSpec = 𝟙 _ := by
    change z ≫ Spec.map (CommRingCat.ofHom (C : K →+*
      MvPolynomial {i : ι // i ≠ j} K)) = _
    rw [← GroupActions.projectiveChartMap_toSpec K ι j, ← Category.assoc, hz]
    exact q.property
  let a : (GroupActions.affineSpaceVariety K {i : ι // i ≠ j}).points := ⟨z, hb⟩
  let x := GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j} a
  let v : ι → K := fun i => if h : i = j then 1 else x ⟨i, h⟩
  have hvj : v j ≠ 0 := by simp [v]
  have hv : v ≠ 0 := fun h => hvj (by rw [h]; rfl)
  have hx : (fun i : {i : ι // i ≠ j} => v i.val / v j) = x := by
    funext i
    simp [v, i.property]
  refine ⟨Projectivization.mk K v hv, ?_⟩
  change projectiveVectorPoint v hv = q
  rw [projectiveVectorPoint_chart v hv j hvj, hx]
  change GroupActions.Variety.mapPoints (GroupActions.projectiveChartMorphism K ι j)
    ((GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm
      (GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j} a)) = q
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  exact hz

/-- Scalar classes of nonzero vectors are the rational points of projective space. -/
def projectivePointsEquiv :
    Projectivization K (ι → K) ≃ (GroupActions.projectiveVariety K ι).points :=
  Equiv.ofBijective projectivePointMap
    ⟨projectivePointMap_injective, projectivePointMap_surjective⟩

/-- The projective class of a vector maps to its homogeneous-evaluation point. -/
theorem projectivePointsEquiv_mk (v : ι → K) (hv : v ≠ 0) :
    projectivePointsEquiv (Projectivization.mk K v hv) = projectiveVectorPoint v hv := rfl

/-- The rational point of a vector class has the standard affine coordinate ratios. -/
theorem projectivePointsEquiv_mk_chart (v : ι → K) (hv : v ≠ 0) (j : ι) (hj : v j ≠ 0) :
    projectivePointsEquiv (Projectivization.mk K v hv) =
      GroupActions.Variety.mapPoints (GroupActions.projectiveChartMorphism K ι j)
        ((GroupActions.affineSpaceVarietyPointsEquiv K {i : ι // i ≠ j}).symm
          (fun i => v i.val / v j)) :=
  projectiveVectorPoint_chart v hv j hj
end GroupActions
