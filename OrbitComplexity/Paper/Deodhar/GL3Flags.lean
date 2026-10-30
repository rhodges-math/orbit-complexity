import OrbitComplexity.Paper.Deodhar.GL3RootProducts
import OrbitComplexity.Paper.Deodhar.ParameterOrbits
import OrbitComplexity.Paper.Deodhar.ComponentWeights
import OrbitComplexity.Paper.Deodhar.ComponentOrbitDimensions
import OrbitComplexity.Paper.Deodhar.Scaling
import OrbitComplexity.BruhatIntervals.Permutations.PositiveRoots
import OrbitComplexity.ReductiveGroups.GLn.GroupData
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import Mathlib.Tactic

/-! # Matrix flags and diagonal action in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K]

variable [IsAlgClosed K]

/-- The invertible matrix representing the s₁1s₁ flag. -/
def decreasingGL (p m : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (decreasingMatrix p m) (by
    simp [decreasingMatrix, Matrix.det_fin_three])

/-- The invertible matrix representing the 111 flag. -/
def positiveGL (a b c : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (positiveMatrix a b c) (by
    simp [positiveMatrix, Matrix.det_fin_three])

private theorem diagonal_mem_torus (t : Fin 3 → Kˣ) :
    (matrixPoints (K := K)).symm (ReductiveGroups.diagGL t) ∈ (GLn.groupData K 3).torusPoints := by
  have h := GLn.diagonal_mem_matrixPoints_torusIdeal (ReductiveGroups.diagGL t)
    (fun i => (t i : K)) (by rfl)
  exact h

private def diagonalPoint (t : Fin 3 → Kˣ) : (GLn.groupData K 3).torusPoints :=
  ⟨(matrixPoints (K := K)).symm (ReductiveGroups.diagGL t), diagonal_mem_torus t⟩

private def matrixFlag (a : GL (Fin 3) K) : flagPoints (GLn.groupData K 3) :=
  flagProjection (GLn.groupData K 3) ((matrixPoints (K := K)).symm a)

omit [IsAlgClosed K] in
private theorem diagonal_decreasing (t : Fin 3 → Kˣ) (p m : K) :
    ReductiveGroups.diagGL t * decreasingGL p m =
      decreasingGL ((t 2 : K) / t 0 * p) ((t 1 : K) / t 0 * m) * ReductiveGroups.diagGL t := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (t i : K))) * decreasingMatrix p m =
    decreasingMatrix ((t 2 : K) / t 0 * p) ((t 1 : K) / t 0 * m) *
      Matrix.diagonal (fun i => (t i : K))
  have hd : Matrix.diagonal (fun i => (t i : K)) =
      !![(t 0 : K), 0, 0; 0, (t 1 : K), 0; 0, 0, (t 2 : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hd]
  exact SchubertOrbits.deodhar_scaling_decreasing _ _ _ p m (Units.ne_zero (t 0))

omit [IsAlgClosed K] in
private theorem diagonal_positive (t : Fin 3 → Kˣ) (a b c : K) :
    ReductiveGroups.diagGL t * positiveGL a b c =
      positiveGL ((t 1 : K) / t 0 * a) ((t 2 : K) / t 1 * b)
        ((t 1 : K) / t 0 * c) * ReductiveGroups.diagGL t := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (t i : K))) * positiveMatrix a b c =
    positiveMatrix ((t 1 : K) / t 0 * a) ((t 2 : K) / t 1 * b)
      ((t 1 : K) / t 0 * c) * Matrix.diagonal (fun i => (t i : K))
  have hd : Matrix.diagonal (fun i => (t i : K)) =
      !![(t 0 : K), 0, 0; 0, (t 1 : K), 0; 0, 0, (t 2 : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hd]
  exact SchubertOrbits.deodhar_scaling_positive _ _ _ a b c
    (Units.ne_zero (t 0)) (Units.ne_zero (t 1))

private theorem flag_mul_borel (a b : (GLn.groupData K 3).points)
    (hb : b ∈ (GLn.groupData K 3).borelPoints) :
    flagProjection (GLn.groupData K 3) (a * b) = flagProjection (GLn.groupData K 3) a := by
  rw [flagProjection_eq_iff]
  have he : (a * b)⁻¹ * a = b⁻¹ := by group
  rw [he]
  exact (GLn.groupData K 3).borelPoints.inv_mem hb

private theorem matrixFlag_diagonal (t : Fin 3 → Kˣ) (a b : GL (Fin 3) K)
    (h : ReductiveGroups.diagGL t * a = b * ReductiveGroups.diagGL t) :
    diagonalPoint t • matrixFlag a = matrixFlag b := by
  change ((matrixPoints (K := K)).symm (ReductiveGroups.diagGL t)) •
    flagProjection (GLn.groupData K 3) ((matrixPoints (K := K)).symm a) = _
  rw [← flagProjection_smul, ← map_mul, h, map_mul]
  exact flag_mul_borel _ _ ((GLn.groupData K 3).torus_le_borel (diagonal_mem_torus t))

private theorem decreasing_flag_action (t : Fin 3 → Kˣ) (p m : K) :
    diagonalPoint t • matrixFlag (decreasingGL p m) =
      matrixFlag (decreasingGL ((t 2 : K) / t 0 * p) ((t 1 : K) / t 0 * m)) :=
  matrixFlag_diagonal t _ _ (diagonal_decreasing t p m)

private theorem positive_flag_action (t : Fin 3 → Kˣ) (a b c : K) :
    diagonalPoint t • matrixFlag (positiveGL a b c) =
      matrixFlag (positiveGL ((t 1 : K) / t 0 * a) ((t 2 : K) / t 1 * b)
        ((t 1 : K) / t 0 * c)) :=
  matrixFlag_diagonal t _ _ (diagonal_positive t a b c)

omit [IsAlgClosed K] in
/-- Diagonal rescaling preserves all nonzero parameter conditions. -/
theorem action_admissible (t : Fin 3 → Kˣ) (p m a b c : K)
    (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (t 2 : K) / t 0 * p ≠ 0 ∧
    (((t 1 : K) / t 0 * m ≠ 0) ↔ m ≠ 0) ∧
    (t 1 : K) / t 0 * a ≠ 0 ∧ (t 2 : K) / t 1 * b ≠ 0 ∧
    (t 1 : K) / t 0 * c ≠ 0 := by
  have hratio (i j : Fin 3) : (t i : K) / t j ≠ 0 :=
    div_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  exact ⟨mul_ne_zero (hratio 2 0) hp, mul_ne_zero_iff_left (hratio 1 0),
    mul_ne_zero (hratio 1 0) ha, mul_ne_zero (hratio 2 1) hb,
    mul_ne_zero (hratio 1 0) hc⟩

variable [CharZero K]

/-- The flag-variety rational point represented by an invertible matrix. -/
def schemeMatrixFlag (A : GL (Fin 3) K) :
    (flagVariety (GLn.groupData K 3)).points :=
  flagVarietyPointsEquiv (GLn.groupData K 3) (matrixFlag A)

/-- The torus rational point with the specified invertible diagonal entries. -/
def schemeDiagonalPoint (t : Fin 3 → Kˣ) :
    (torusVariety (GLn.groupData K 3)).points :=
  (torusPointsMulEquiv (GLn.groupData K 3)).symm (diagonalPoint t)

/-- Diagonal torus action rescales the two s₁1s₁ flag parameters. -/
theorem decreasing_scheme_action (t : Fin 3 → Kˣ) (p m : K) :
    schemeDiagonalPoint t • schemeMatrixFlag (decreasingGL p m) =
      schemeMatrixFlag (decreasingGL ((t 2 : K) / t 0 * p) ((t 1 : K) / t 0 * m)) := by
  rw [schemeMatrixFlag, torusFlag_smul, schemeDiagonalPoint, MulEquiv.apply_symm_apply]
  change flagVarietyPointsEquiv (GLn.groupData K 3)
    (diagonalPoint t • matrixFlag (decreasingGL p m)) = _
  exact congrArg (flagVarietyPointsEquiv (GLn.groupData K 3)) (decreasing_flag_action t p m)

/-- Diagonal torus action rescales the three 111 flag parameters. -/
theorem positive_scheme_action (t : Fin 3 → Kˣ) (a b c : K) :
    schemeDiagonalPoint t • schemeMatrixFlag (positiveGL a b c) =
      schemeMatrixFlag (positiveGL ((t 1 : K) / t 0 * a) ((t 2 : K) / t 1 * b)
        ((t 1 : K) / t 0 * c)) := by
  rw [schemeMatrixFlag, torusFlag_smul, schemeDiagonalPoint, MulEquiv.apply_symm_apply]
  change flagVarietyPointsEquiv (GLn.groupData K 3)
    (diagonalPoint t • matrixFlag (positiveGL a b c)) = _
  exact congrArg (flagVarietyPointsEquiv (GLn.groupData K 3)) (positive_flag_action t a b c)

end SchubertOrbits.GL3
