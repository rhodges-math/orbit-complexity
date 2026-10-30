import OrbitComplexity.Paper.Deodhar.GL3Weights
import OrbitComplexity.Paper.Deodhar.GL3Subwords
import OrbitComplexity.Paper.Deodhar.GL3Roots
import OrbitComplexity.ReductiveGroups.GLn.RootCoordinates
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

/-! # Root products in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

private theorem selected_matrix
    (expression : Subexpression (matrixWord (K := K)))
    (q : {j : Fin (matrixWord (K := K)).length //
      j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) expression ∪
        negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) expression})
    (i j : Fin 3) (hij : i ≠ j)
    (hχ : SchubertOrbits.subwordCharacter (GLn.groupData K 3) expression q =
      matrixUnitWeight i j) :
    ∃ a : K, a ≠ 0 ∧ ∀ t : K,
      (pointsMulEquiv 3 (gaParameterPoint
        (SchubertGeometry.subwordRootMap (GLn.groupData K 3) expression q) t) :
          Matrix (Fin 3) (Fin 3) K) = 1 + (t * a) • Matrix.single i j 1 := by
  apply rootMap_matrix (K := K) 3 i j hij
    (SchubertGeometry.subwordRootMap (GLn.groupData K 3) expression q)
  · change _ ∈ affineGroupCharacterWeightSpace (GLn.groupData K 3).torusSplit
      ((GLn.groupData K 3).rootCharacter (matrixRoot 3 i j hij))
    rw [rootCharacter_matrixRoot, ← hχ]
    exact SchubertOrbits.subwordRootMap_tangent_mem (GLn.groupData K 3) expression q
  · exact SchubertGeometry.subwordRootMap_tangent_ne_zero (GLn.groupData K 3) expression q

private theorem decreasing_coefficients :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ t : K, (pointsMulEquiv 3 (gaParameterPoint
        (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
          decreasingJ1) t) : Matrix (Fin 3) (Fin 3) K) =
            1 + (t * a) • Matrix.single 2 0 1) ∧
      (∀ t : K, (pointsMulEquiv 3 (gaParameterPoint
        (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
          decreasingJ2) t) : Matrix (Fin 3) (Fin 3) K) =
            1 + (t * b) • Matrix.single 1 0 1) := by
  obtain ⟨a, ha0, ha⟩ := selected_matrix decreasingExpression decreasingJ1 2 0
    (by decide) (decreasing_character1 (K := K))
  obtain ⟨b, hb0, hb⟩ := selected_matrix decreasingExpression decreasingJ2 1 0
    (by decide) (decreasing_character2 (K := K))
  exact ⟨a, b, ha0, hb0, ha, hb⟩

private theorem positive_coefficients :
    ∃ a : Fin 3 → K, (∀ j, a j ≠ 0) ∧ ∀ j t,
      (pointsMulEquiv 3 (gaParameterPoint
        (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
          (positiveJ j)) t) : Matrix (Fin 3) (Fin 3) K) =
            1 + (t * a j) • Matrix.single
              ((![1, 2, 1] : Fin 3 → Fin 3) j) ((![0, 1, 0] : Fin 3 → Fin 3) j) 1 := by
  have hall (j : Fin 3) : ∃ c : K, c ≠ 0 ∧ ∀ t,
      (pointsMulEquiv 3 (gaParameterPoint
        (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
          (positiveJ j)) t) : Matrix (Fin 3) (Fin 3) K) =
            1 + (t * c) • Matrix.single
              ((![1, 2, 1] : Fin 3 → Fin 3) j) ((![0, 1, 0] : Fin 3 → Fin 3) j) 1 := by
    fin_cases j
    · exact selected_matrix positiveExpression (positiveJ 0) 1 0 (by decide)
        (positive_character (K := K) 0)
    · exact selected_matrix positiveExpression (positiveJ 1) 2 1 (by decide)
        (positive_character (K := K) 1)
    · exact selected_matrix positiveExpression (positiveJ 2) 1 0 (by decide)
        (positive_character (K := K) 2)
  choose a ha0 ha using hall
  exact ⟨a, ha0, ha⟩

/-- The two-parameter lower-unipotent matrix for s₁1s₁. -/
def decreasingMatrix (p m : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; -m, 1, 0; -p, 0, 1]

/-- The three-parameter lower-unipotent matrix for 111. -/
def positiveMatrix (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; a + c, 1, 0; b * c, b, 1]

omit [IsAlgClosed K] [CharZero K] in
private theorem elementary_decreasing (a b : K) :
    (1 + a • Matrix.single 2 0 (1 : K)) *
      (1 + b • Matrix.single 1 0 (1 : K)) =
        decreasingMatrix (-a) (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [decreasingMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply]

omit [IsAlgClosed K] [CharZero K] in
private theorem elementary_positive (a b c : K) :
    (1 + a • Matrix.single 1 0 (1 : K)) *
      ((1 + b • Matrix.single 2 1 (1 : K)) *
        (1 + c • Matrix.single 1 0 (1 : K))) =
          positiveMatrix a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.single_apply, Matrix.one_apply]

/-- General-linear coordinate-algebra points are invertible matrices. -/
def matrixPoints : (GLn.groupData K 3).points ≃* GL (Fin 3) K :=
  pointsMulEquiv 3

attribute [local instance] matrixWord_neZero

private theorem word_ofFn {A : Type*} (f : Fin (matrixWord (K := K)).length → A) :
    List.ofFn f = [f 0, f 1, f 2] := by
  rfl

private theorem matrixWord_get0 :
    (matrixWord (K := K))[(0 : Fin (matrixWord (K := K)).length).val] = simple01 := rfl

private theorem matrixWord_get1 :
    (matrixWord (K := K))[(1 : Fin (matrixWord (K := K)).length).val] = simple12 := rfl

private theorem matrixWord_get2 :
    (matrixWord (K := K))[(2 : Fin (matrixWord (K := K)).length).val] = simple01 := rfl

private theorem decreasing_prefix_factors (p : Fin (matrixWord (K := K)).length → K) :
    SchubertGeometry.deodharPrefix (GLn.groupData K 3) decreasingExpression p 3 =
      gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3)
        decreasingExpression decreasingJ1) (p 1) *
      gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3)
        decreasingExpression decreasingJ2) (p 2) := by
  have he0 : (0 : Fin (matrixWord (K := K)).length) ∉ equalSteps (weylCoxeterSystem (GLn.groupData K
    3).rootBase) decreasingExpression :=
    (Set.ext_iff.mp (decreasing_equal (K := K)) 0).not.mpr (by
      intro h
      have hv := congrArg Fin.val h
      change (0 : ℕ) = 1 at hv
      exact (by decide : (0 : ℕ) ≠ 1) hv)
  have he1 : (1 : Fin (matrixWord (K := K)).length) ∈ equalSteps (weylCoxeterSystem (GLn.groupData K
    3).rootBase) decreasingExpression :=
    (Set.ext_iff.mp (decreasing_equal (K := K)) 1).mpr rfl
  have hn0 : (0 : Fin (matrixWord (K := K)).length) ∉ negativeSteps (weylCoxeterSystem
    (GLn.groupData K 3).rootBase) decreasingExpression :=
    (Set.ext_iff.mp (decreasing_negative (K := K)) 0).not.mpr (by
      intro h
      have hv := congrArg Fin.val h
      change (0 : ℕ) = 2 at hv
      exact (by decide : (0 : ℕ) ≠ 2) hv)
  have hn1 : (1 : Fin (matrixWord (K := K)).length) ∉ negativeSteps (weylCoxeterSystem
    (GLn.groupData K 3).rootBase) decreasingExpression :=
    (Set.ext_iff.mp (decreasing_negative (K := K)) 1).not.mpr (by
      intro h
      have hv := congrArg Fin.val h
      change (1 : ℕ) = 2 at hv
      exact (by decide : (1 : ℕ) ≠ 2) hv)
  have hn2 : (2 : Fin (matrixWord (K := K)).length) ∈ negativeSteps (weylCoxeterSystem
    (GLn.groupData K 3).rootBase) decreasingExpression :=
    (Set.ext_iff.mp (decreasing_negative (K := K)) 2).mpr rfl
  have h1 := SchubertGeometry.subwordRootMap_point (GLn.groupData K 3) decreasingExpression p
    decreasingJ1
  have h2 := SchubertGeometry.subwordRootMap_point (GLn.groupData K 3) decreasingExpression p
    decreasingJ2
  change gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
    decreasingJ1)
    (p 1) = SchubertGeometry.subwordRepresentative (GLn.groupData K 3) decreasingExpression 1 *
      SchubertGeometry.deodharRootElement (GLn.groupData K 3) decreasingExpression p 1 *
        (SchubertGeometry.subwordRepresentative (GLn.groupData K 3) decreasingExpression 1)⁻¹ at h1
  change gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
    decreasingJ2)
    (p 2) = SchubertGeometry.subwordRepresentative (GLn.groupData K 3) decreasingExpression 2 *
      SchubertGeometry.deodharRootElement (GLn.groupData K 3) decreasingExpression p 2 *
        (SchubertGeometry.subwordRepresentative (GLn.groupData K 3) decreasingExpression 2)⁻¹ at h2
  rw [h1, h2]
  simp only [SchubertGeometry.deodharPrefix, SchubertGeometry.subwordRepresentative,
    word_ofFn, List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil]
  simp only [SchubertGeometry.deodharStep, SchubertGeometry.deodharRootElement,
    SchubertGeometry.subwordStepPoint, he0, he1, hn0, hn1, hn2,
    ↓reduceIte, matrixWord_get0, matrixWord_get1, matrixWord_get2, mul_one, one_mul]
  group

private theorem positive_prefix_factors (p : Fin (matrixWord (K := K)).length → K) :
    SchubertGeometry.deodharPrefix (GLn.groupData K 3) positiveExpression p 3 =
      gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3)
        positiveExpression (positiveJ 0)) (p 0) *
      (gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3)
        positiveExpression (positiveJ 1)) (p 1) *
      gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3)
        positiveExpression (positiveJ 2)) (p 2)) := by
  have he (j : Fin (matrixWord (K := K)).length) : j ∈ equalSteps (weylCoxeterSystem (GLn.groupData
    K 3).rootBase) positiveExpression :=
    (Set.ext_iff.mp (positive_equal (K := K)) j).mpr trivial
  have hn (j : Fin (matrixWord (K := K)).length) : j ∉ negativeSteps (weylCoxeterSystem
    (GLn.groupData K 3).rootBase) positiveExpression := by
    intro hj
    exact (Set.ext_iff.mp (positive_negative (K := K)) j).mp hj
  have h0 := SchubertGeometry.subwordRootMap_point (GLn.groupData K 3) positiveExpression p
    (positiveJ 0)
  have h1 := SchubertGeometry.subwordRootMap_point (GLn.groupData K 3) positiveExpression p
    (positiveJ 1)
  have h2 := SchubertGeometry.subwordRootMap_point (GLn.groupData K 3) positiveExpression p
    (positiveJ 2)
  change gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
    (positiveJ 0))
    (p 0) = SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 0 *
      SchubertGeometry.deodharRootElement (GLn.groupData K 3) positiveExpression p 0 *
        (SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 0)⁻¹ at h0
  change gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
    (positiveJ 1))
    (p 1) = SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 1 *
      SchubertGeometry.deodharRootElement (GLn.groupData K 3) positiveExpression p 1 *
        (SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 1)⁻¹ at h1
  change gaParameterPoint (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
    (positiveJ 2))
    (p 2) = SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 2 *
      SchubertGeometry.deodharRootElement (GLn.groupData K 3) positiveExpression p 2 *
        (SchubertGeometry.subwordRepresentative (GLn.groupData K 3) positiveExpression 2)⁻¹ at h2
  rw [h0, h1, h2]
  simp only [SchubertGeometry.deodharPrefix, SchubertGeometry.subwordRepresentative,
    word_ofFn, List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil]
  simp only [SchubertGeometry.deodharStep, SchubertGeometry.deodharRootElement,
    SchubertGeometry.subwordStepPoint, he, hn, ↓reduceIte,
    matrixWord_get0, matrixWord_get1, matrixWord_get2, mul_one, one_mul, inv_one]

/-- The s₁1s₁ group product has the stated two-parameter matrix form. -/
theorem decreasing_prefix_matrix :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ ∀ p : Fin (matrixWord (K := K)).length → K,
      (matrixPoints (K := K) (SchubertGeometry.deodharPrefix (GLn.groupData K 3)
        decreasingExpression p 3) : Matrix (Fin 3) (Fin 3) K) =
          decreasingMatrix (-(p 1 * a)) (-(p 2 * b)) := by
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ := decreasing_coefficients (K := K)
  change ∀ t : K, (matrixPoints (gaParameterPoint
    (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression decreasingJ1) t) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (t * a) • Matrix.single 2 0 1 at ha
  change ∀ t : K, (matrixPoints (gaParameterPoint
    (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression decreasingJ2) t) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (t * b) • Matrix.single 1 0 1 at hb
  refine ⟨a, b, ha0, hb0, fun p => ?_⟩
  rw [decreasing_prefix_factors, map_mul]
  change (matrixPoints (K := K) (gaParameterPoint
      (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
        decreasingJ1) (p 1)) : Matrix (Fin 3) (Fin 3) K) *
    (matrixPoints (K := K) (gaParameterPoint
      (SchubertGeometry.subwordRootMap (GLn.groupData K 3) decreasingExpression
        decreasingJ2) (p 2)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [ha, hb]
  exact elementary_decreasing (p 1 * a) (p 2 * b)

/-- The 111 group product has the stated three-parameter matrix form. -/
theorem positive_prefix_matrix :
    ∃ a : Fin 3 → K, (∀ j, a j ≠ 0) ∧ ∀ p : Fin (matrixWord (K := K)).length → K,
      (matrixPoints (K := K) (SchubertGeometry.deodharPrefix (GLn.groupData K 3)
        positiveExpression p 3) : Matrix (Fin 3) (Fin 3) K) =
          positiveMatrix (p 0 * a 0) (p 1 * a 1) (p 2 * a 2) := by
  obtain ⟨a, ha0, ha⟩ := positive_coefficients (K := K)
  change ∀ j : Fin 3, ∀ t : K, (matrixPoints (gaParameterPoint
    (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression (positiveJ j)) t) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (t * a j) • Matrix.single
        ((![1, 2, 1] : Fin 3 → Fin 3) j) ((![0, 1, 0] : Fin 3 → Fin 3) j) 1 at ha
  refine ⟨a, ha0, fun p => ?_⟩
  rw [positive_prefix_factors, map_mul, map_mul]
  change (matrixPoints (K := K) (gaParameterPoint
      (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
        (positiveJ 0)) (p 0)) : Matrix (Fin 3) (Fin 3) K) *
    ((matrixPoints (K := K) (gaParameterPoint
      (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
        (positiveJ 1)) (p 1)) : Matrix (Fin 3) (Fin 3) K) *
    (matrixPoints (K := K) (gaParameterPoint
      (SchubertGeometry.subwordRootMap (GLn.groupData K 3) positiveExpression
        (positiveJ 2)) (p 2)) : Matrix (Fin 3) (Fin 3) K)) = _
  rw [ha 0, ha 1, ha 2]
  exact elementary_positive (p 0 * a 0) (p 1 * a 1) (p 2 * a 2)

end SchubertOrbits.GL3
