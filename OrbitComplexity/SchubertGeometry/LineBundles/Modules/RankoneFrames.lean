import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Coroot
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing

/-! # Rank-one frames for the two projective charts -/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups TauCeti
open scoped Matrix
universe u

private def diagonalUnit {R : Type u} [CommRing R] (a : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![(a : R), 0; 0, (↑(a⁻¹) : R)], by simp [Matrix.det_fin_two]⟩

private theorem matrix_frame_overlap {R : Type u} [CommRing R] (a : Rˣ) :
    Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (↑(a⁻¹) : R) *
        (diagonalUnit a * Matrix.SpecialLinearGroup.transvection
          (zero_ne_one : (0 : Fin 2) ≠ 1) (-↑(a⁻¹) : R)) =
      Matrix.SpecialLinearGroup.transvection
        (zero_ne_one : (0 : Fin 2) ≠ 1) (a : R) * sl2Weyl R := by
  apply Subtype.ext
  change ((1 + Matrix.single (1 : Fin 2) 0 (↑(a⁻¹) : R)) *
    (!![(a : R), 0; 0, (↑(a⁻¹) : R)] *
      (1 + Matrix.single (0 : Fin 2) 1 (-↑(a⁻¹) : R)))) =
    (1 + Matrix.single (0 : Fin 2) 1 (a : R)) * !![0, -1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.single]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The chosen simple root frames differ by the coroot and an upper-root factor. -/
theorem simpleFrame_overlap (i : G.rootBase.support) (a : Kˣ) :
    gaParameterPoint (G.negativeSimpleRootMap i) (↑(a⁻¹) : K) *
        (Coroot.simpleCorootPoint G i a *
          gaParameterPoint (G.simpleRootMap i) (-↑(a⁻¹) : K)) =
      gaParameterPoint (G.simpleRootMap i) (a : K) * (G.reflectionPoint i.val)⁻¹ := by
  have hd : diagonalUnit a = Matrix.SpecialLinearGroup.diag2 (a : K) (Units.ne_zero a) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalUnit, Matrix.SpecialLinearGroup.diag2_coe]
  have h := congrArg (G.simpleSl2Points i) (matrix_frame_overlap a)
  rw [map_mul, map_mul, map_mul, hd, G.simpleSl2Points_upper,
    G.simpleSl2Points_lower, G.simpleSl2Points_upper, G.simpleSl2Points_diagonal,
    G.simpleSl2Points_weyl] at h
  exact h

end SchubertGeometry
