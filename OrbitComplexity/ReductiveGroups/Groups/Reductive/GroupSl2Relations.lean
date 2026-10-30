import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Points

/-! # Simple-root interchange -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open scoped Matrix

universe u
variable {K : Type u} [Field K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem elementary_interchange :
    Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) *
        Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : K) *
        Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) =
      Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : K) *
        Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : K) *
        Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : K) := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

variable [CharZero K] [IsAlgClosed K]

/-- The chosen simple-root parameters satisfy the rank-one interchange identity. -/
theorem simpleRoot_interchange (i : G.rootBase.support) :
    gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) =
      gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (-1 : K)) := by
  have h := congrArg (G.simpleSl2Points i) (elementary_interchange (K := K))
  simpa only [map_mul, simpleSl2Points_upper, simpleSl2Points_lower] using h

end ReductiveGroups.ReductiveGroupData
