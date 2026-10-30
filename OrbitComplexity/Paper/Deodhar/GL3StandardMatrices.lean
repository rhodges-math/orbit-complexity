import OrbitComplexity.Paper.Deodhar.GL3RootProducts
import OrbitComplexity.Paper.Deodhar.GL3Subwords
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

/-! # Standard matrix families in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] matrixWord_neZero

private theorem decreasing_prefix_image :
    {M : Matrix (Fin 3) (Fin 3) K | ∃ p : Fin (matrixWord (K := K)).length → K,
      (∀ j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
        decreasingExpression, p j ≠ 0) ∧
      (matrixPoints (K := K) (SchubertGeometry.deodharPrefix (GLn.groupData K 3)
        decreasingExpression p 3) : Matrix (Fin 3) (Fin 3) K) = M} =
      {M | ∃ p m : K, p ≠ 0 ∧ decreasingMatrix p m = M} := by
  obtain ⟨a, b, ha0, hb0, hmatrix⟩ := decreasing_prefix_matrix (K := K)
  ext M
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨-(p 1 * a), -(p 2 * b), neg_ne_zero.mpr (mul_ne_zero ?_ ha0), ?_⟩
    · apply hp 1
      rw [decreasing_equal]
      rfl
    · exact (hmatrix p).symm
  · rintro ⟨p, m, hp, rfl⟩
    let q : Fin (matrixWord (K := K)).length → K := ![0, -p / a, -m / b]
    refine ⟨q, ?_, ?_⟩
    · intro j hj
      rw [decreasing_equal, Set.mem_singleton_iff] at hj
      subst j
      exact div_ne_zero (neg_ne_zero.mpr hp) ha0
    · rw [hmatrix]
      change decreasingMatrix (-((-p / a) * a)) (-((-m / b) * b)) = _
      rw [div_mul_cancel₀ _ ha0, div_mul_cancel₀ _ hb0, neg_neg, neg_neg]

private theorem positive_prefix_image :
    {M : Matrix (Fin 3) (Fin 3) K | ∃ p : Fin (matrixWord (K := K)).length → K,
      (∀ j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
        positiveExpression, p j ≠ 0) ∧
      (matrixPoints (K := K) (SchubertGeometry.deodharPrefix (GLn.groupData K 3)
        positiveExpression p 3) : Matrix (Fin 3) (Fin 3) K) = M} =
      {M | ∃ a b c : K, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ positiveMatrix a b c = M} := by
  obtain ⟨a, ha0, hmatrix⟩ := positive_prefix_matrix (K := K)
  ext M
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hn (j : Fin (matrixWord (K := K)).length) : p j ≠ 0 := by
      apply hp j
      rw [positive_equal]
      trivial
    exact ⟨p 0 * a 0, p 1 * a 1, p 2 * a 2,
      mul_ne_zero (hn 0) (ha0 0), mul_ne_zero (hn 1) (ha0 1),
      mul_ne_zero (hn 2) (ha0 2), (hmatrix p).symm⟩
  · rintro ⟨p, q, r, hp, hq, hr, rfl⟩
    let z : Fin (matrixWord (K := K)).length → K := ![p / a 0, q / a 1, r / a 2]
    refine ⟨z, ?_, ?_⟩
    · intro j _
      fin_cases j
      · exact div_ne_zero hp (ha0 0)
      · exact div_ne_zero hq (ha0 1)
      · exact div_ne_zero hr (ha0 2)
    · rw [hmatrix]
      change positiveMatrix ((p / a 0) * a 0) ((q / a 1) * a 1)
        ((r / a 2) * a 2) = _
      rw [div_mul_cancel₀ _ (ha0 0), div_mul_cancel₀ _ (ha0 1), div_mul_cancel₀ _ (ha0 2)]

private theorem standard_matrix_image
    (expression : Subexpression (matrixWord (K := K)))
    (hd : IsDistinguished (weylCoxeterSystem (GLn.groupData K 3).rootBase) expression) :
    Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3)
      expression matrixWord_reduced hd).points =>
      (matrixPoints (K := K) ((GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
            matrixWord_reduced hd)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) expression
            matrixWord_reduced hd) x)) :
            Matrix (Fin 3) (Fin 3) K)) =
      {M | ∃ p : Fin (matrixWord (K := K)).length → K,
        (∀ j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
          expression, p j ≠ 0) ∧
        (matrixPoints (K := K) (SchubertGeometry.deodharPrefix (GLn.groupData K 3)
          expression p 3) : Matrix (Fin 3) (Fin 3) K) = M} := by
  have hr := SchubertGeometry.deodharStandard_points (GLn.groupData K 3) expression
    matrixWord_reduced hd
  ext M
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
            matrixWord_reduced hd)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) expression
            matrixWord_reduced hd) x) ∈
          Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
            matrixWord_reduced hd).points => (GroupActions.reductivePointsEquiv (GLn.groupData K
              3)).symm
              (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
            matrixWord_reduced hd)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) expression
            matrixWord_reduced hd) x)) := ⟨x, rfl⟩
    rw [hr] at hx
    obtain ⟨p, hp, he⟩ := hx
    exact ⟨p, hp, congrArg (fun g : (GLn.groupData K 3).points =>
      (matrixPoints (K := K) g : Matrix (Fin 3) (Fin 3) K)) he⟩
  · rintro ⟨p, hp, rfl⟩
    have hx : SchubertGeometry.deodharPrefix (GLn.groupData K 3) expression p 3 ∈
        Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
          matrixWord_reduced hd).points => (GroupActions.reductivePointsEquiv (GLn.groupData K
            3)).symm
            (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) expression
            matrixWord_reduced hd)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) expression
            matrixWord_reduced hd) x)) := by
      rw [hr]
      exact ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ := hx
    exact ⟨x, congrArg (fun g : (GLn.groupData K 3).points =>
      (matrixPoints (K := K) g : Matrix (Fin 3) (Fin 3) K)) hx⟩

/-- The s₁1s₁ standard-form variety has exactly the displayed matrix family. -/
theorem decreasing_standard_matrices :
    Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3)
      decreasingExpression matrixWord_reduced decreasing_distinguished).points =>
      (matrixPoints (K := K) ((GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) decreasingExpression
            matrixWord_reduced decreasing_distinguished)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) decreasingExpression
            matrixWord_reduced decreasing_distinguished) x)) : Matrix (Fin 3) (Fin 3) K)) =
      {M | ∃ p m : K, p ≠ 0 ∧ decreasingMatrix p m = M} :=
  (standard_matrix_image decreasingExpression decreasing_distinguished).trans
    decreasing_prefix_image

/-- The 111 standard-form variety has exactly the displayed matrix family. -/
theorem positive_standard_matrices :
    Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3)
      positiveExpression matrixWord_reduced positive_distinguished).points =>
      (matrixPoints (K := K) ((GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) positiveExpression
            matrixWord_reduced positive_distinguished)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) positiveExpression
            matrixWord_reduced positive_distinguished) x)) : Matrix (Fin 3) (Fin 3) K)) =
      {M | ∃ a b c : K, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ positiveMatrix a b c = M} :=
  (standard_matrix_image positiveExpression positive_distinguished).trans
    positive_prefix_image

end SchubertOrbits.GL3
