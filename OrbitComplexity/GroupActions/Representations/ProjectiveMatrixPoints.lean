import OrbitComplexity.GroupActions.Representations.ProjectiveMatrix
import OrbitComplexity.GroupActions.Representations.ProjectivePoints

/-! # Projective matrix morphisms on rational points

Homogeneous polynomial evaluation identifies the point map of matrix substitution with
ordinary multiplication of coordinate vectors.
-/

noncomputable section
namespace GroupActions
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Matrix
universe u
variable {K H ι : Type u} [Field K] [CommRing H] [Algebra K H]
  [Fintype ι] [DecidableEq ι]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [DecidableEq ι] in
private theorem eval_substitution (a : Matrix ι ι K) (v : ι → K)
    (p : MvPolynomial ι K) :
    eval v (projectiveMatrixHom a p) = eval (a *ᵥ v) p := by
  have he : (eval v).comp (projectiveMatrixHom a).toRingHom = eval (a *ᵥ v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change eval v (projectiveMatrixHom a (C r)) = eval (a *ᵥ v) (C r)
      simp only [projectiveMatrixHom_C, Algebra.algebraMap_self_apply, eval_C]
    · intro i
      change eval v (projectiveMatrixHom a (X i)) = _
      simp only [projectiveMatrixHom_X, map_sum, map_mul, eval_C, eval_X]
      rfl
  exact DFunLike.congr_fun he p

/-- A matrix unit acts on projective space by a morphism over the field. -/
def projectiveMatrixMorphism (a : Matrix.GeneralLinearGroup ι K) :
    (projectiveVariety K ι).toOver ⟶ (projectiveVariety K ι).toOver :=
  Over.homMk (projectiveMatrixMap (R := K) a) (by
    change projectiveMatrixMap a ≫ projectiveToSpec K ι = projectiveToSpec K ι
    simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Category.comp_id] using projectiveMatrixMap_toSpec (R := K) a)

omit [Fintype ι] [DecidableEq ι] in
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

/-- The projective matrix morphism sends vector points to matrix-vector points. -/
theorem projectiveMatrixMorphism_points [IsAlgClosed K]
    (a : Matrix.GeneralLinearGroup ι K) (v : ι → K) (hv : v ≠ 0) :
    Variety.mapPoints (projectiveMatrixMorphism a) (projectiveVectorPoint v hv) =
      projectiveVectorPoint ((a : Matrix ι ι K) *ᵥ v)
        (by simpa only [Matrix.mulVec_zero] using
          (Matrix.mulVec_injective_of_isUnit a.isUnit).ne hv) := by
  apply (projectiveVariety K ι).pointMap_injective
  rw [Variety.pointMap_mapPoints]
  let x : ProjectiveSpectrum (homogeneousSubmodule ι K) :=
    (projectiveVariety K ι).pointMap (projectiveVectorPoint v hv)
  let y : ProjectiveSpectrum (homogeneousSubmodule ι K) :=
    (projectiveVariety K ι).pointMap (projectiveVectorPoint ((a : Matrix ι ι K) *ᵥ v)
      (by simpa only [Matrix.mulVec_zero] using
        (Matrix.mulVec_injective_of_isUnit a.isUnit).ne hv))
  let z : ProjectiveSpectrum (homogeneousSubmodule ι K) := projectiveMatrixMap (R := K) a x
  change z = y
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
    have he : p = C (p.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp.totalDegree_le)
    rw [he]
    exact (constant_mem z _).trans (constant_mem y _).symm
  | succ n =>
    calc
      p ∈ z.asHomogeneousIdeal ↔ projectiveMatrixHom (a : Matrix ι ι K) p ∈
          x.asHomogeneousIdeal := projectiveMatrixMap_mem a x p
      _ ↔ eval v (projectiveMatrixHom (a : Matrix ι ι K) p) = 0 :=
        projectiveVectorPoint_mem v hv (n + 1) (Nat.succ_pos n) _
          ((projectiveMatrixHom (a : Matrix ι ι K)).map_mem hp)
      _ ↔ eval ((a : Matrix ι ι K) *ᵥ v) p = 0 := by rw [eval_substitution]
      _ ↔ p ∈ y.asHomogeneousIdeal :=
        (projectiveVectorPoint_mem _ _ (n + 1) (Nat.succ_pos n) p hp).symm

end GroupActions
