import OrbitComplexity.Paper.Deodhar.GL3Weyl
import Mathlib.Analysis.Complex.Polynomial.Basic
import OrbitComplexity.Paper.Deodhar.GL3OrbitDimensions
import OrbitComplexity.Paper.Deodhar.GL3Flags
import OrbitComplexity.Paper.Deodhar.GL3ParameterRanks
import OrbitComplexity.Paper.Deodhar.GL3StandardMatrices
import OrbitComplexity.Paper.Deodhar.GL3RootProducts
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

/-! # Rank-three Deodhar matrix example -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open SchubertOrbits.GL3
open scoped Classical

noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The rank-three Weyl permutations, matrix families, weights and torus orbits. -/
theorem deodhar_example :
    (∃ e : (GLn.groupData K 3).weylGroup ≃* Equiv.Perm (Fin 3),
      e (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root01) =
        Equiv.swap 0 1 ∧
      e (RootPairing.weylGroup.ofIdx (GLn.groupData K 3).rootSystem root12) =
        Equiv.swap 1 2 ∧
      e (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) = Equiv.swap 0 2 ∧
      (∀ i : Fin 3, e (simpleWeylWord (GLn.groupData K 3).rootBase matrixWord) i =
        (![2, 1, 0] : Fin 3 → Fin 3) i) ∧
      (∀ i : Fin 3, e 1 i = (![0, 1, 2] : Fin 3 → Fin 3) i) ∧
      simpleWeylWord (GLn.groupData K 3).rootBase matrixWord =
        (GLn.groupData K 3).longestElement
    ) ∧ (
    (Module.finrank ℝ (Submodule.span ℝ (Set.range
      (parameterWeight (K := K) decreasingExpression))) = 2) ∧
    (Module.finrank ℝ (Submodule.span ℝ (Set.range
      (parameterWeight (K := K) positiveExpression))) = 2) ∧
    (∀ parameter coordinate : K,
    (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 1, 0; 0, parameter, 1] *
      (!![1, coordinate, 0; 0, 1, 0; 0, 0, 1] * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) =
        !![1, 0, 0; -coordinate, 1, 0; -parameter, 0, 1]) ∧
    (∀ first second third : K,
    (!![1, 0, 0; first, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 1, 0; 0, second, 1] * !![1, 0, 0; third, 1, 0; 0, 0, 1] =
        !![1, 0, 0; first + third, 1, 0; second * third, second, 1]) ∧
    ((GLn.groupData K 3).rootCharacter (simple01 (K := K)).val = matrixUnitWeight 0 1) ∧
    ((GLn.groupData K 3).rootCharacter (simple12 (K := K)).val = matrixUnitWeight 1 2) ∧
    ((weylCoxeterSystem (GLn.groupData K 3).rootBase).IsReduced matrixWord) ∧
    (IsDistinguished (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (decreasingExpression (K := K))) ∧
    (IsDistinguished (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K))) ∧
    (IsPositive (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K))) ∧
    (∀ expression : Subexpression (matrixWord (K := K)),
    expression.prefixProd (weylCoxeterSystem (GLn.groupData K 3).rootBase) 3 = 1 ↔
      expression = decreasingExpression ∨ expression = positiveExpression) ∧
    (Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3)
      decreasingExpression matrixWord_reduced decreasing_distinguished).points =>
      (matrixPoints (K := K) ((GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) decreasingExpression
            matrixWord_reduced decreasing_distinguished)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) decreasingExpression
            matrixWord_reduced decreasing_distinguished) x)) : Matrix (Fin 3) (Fin 3) K)) =
      {M | ∃ p m : K, p ≠ 0 ∧ decreasingMatrix p m = M}) ∧
    (Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData K 3)
      positiveExpression matrixWord_reduced positive_distinguished).points =>
      (matrixPoints (K := K) ((GroupActions.reductivePointsEquiv (GLn.groupData K 3)).symm
        (GroupActions.Variety.mapPoints
          (X := SchubertGeometry.deodharStandardVariety (GLn.groupData K 3) positiveExpression
            matrixWord_reduced positive_distinguished)
          (Y := GroupActions.reductiveVariety (GLn.groupData K 3))
          (SchubertGeometry.deodharStandardInclusion (GLn.groupData K 3) positiveExpression
            matrixWord_reduced positive_distinguished) x)) : Matrix (Fin 3) (Fin 3) K)) =
      {M | ∃ a b c : K, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ positiveMatrix a b c = M}) ∧
    (SchubertOrbits.subwordCharacter (GLn.groupData K 3) decreasingExpression
      decreasingJ1 = matrixUnitWeight 2 0) ∧
    (SchubertOrbits.subwordCharacter (GLn.groupData K 3) decreasingExpression
      decreasingJ2 = matrixUnitWeight 1 0) ∧
    (∀ j : Fin 3,
    SchubertOrbits.subwordCharacter (GLn.groupData K 3) positiveExpression
      (positiveJ j) =
        (![matrixUnitWeight 1 0, matrixUnitWeight 2 1, matrixUnitWeight 1 0] :
          Fin 3 → (GLn.groupData K 3).characters) j) ∧
    (Module.finrank ℝ (Submodule.span ℝ (Set.range decreasingWeights)) = 2) ∧
    (Module.finrank ℝ (Submodule.span ℝ (Set.range positiveWeights)) = 2) ∧
    (∀ (t : Fin 3 → Kˣ) (p m : K),
    schemeDiagonalPoint t • schemeMatrixFlag (decreasingGL p m) =
      schemeMatrixFlag (decreasingGL ((t 2 : K) / t 0 * p) ((t 1 : K) / t 0 * m))) ∧
    (∀ (t : Fin 3 → Kˣ) (a b c : K),
    schemeDiagonalPoint t • schemeMatrixFlag (positiveGL a b c) =
      schemeMatrixFlag (positiveGL ((t 1 : K) / t 0 * a) ((t 2 : K) / t 1 * b)
        ((t 1 : K) / t 0 * c))) ∧
    (∀ (t : Fin 3 → Kˣ) (p m a b c : K),
    p ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
    (t 2 : K) / t 0 * p ≠ 0 ∧
    (((t 1 : K) / t 0 * m ≠ 0) ↔ m ≠ 0) ∧
    (t 1 : K) / t 0 * a ≠ 0 ∧ (t 2 : K) / t 1 * b ≠ 0 ∧
    (t 1 : K) / t 0 * c ≠ 0) ∧
    (∀ (p m : K), p ≠ 0 →
    orbitNatDim (torusVariety (GLn.groupData K 3)) (flagVariety (GLn.groupData K 3))
      (schemeMatrixFlag (decreasingGL p m)) = if m = 0 then 1 else 2) ∧
    (∀ (a b c : K), a ≠ 0 → b ≠ 0 → c ≠ 0 →
    orbitNatDim (torusVariety (GLn.groupData K 3)) (flagVariety (GLn.groupData K 3))
      (schemeMatrixFlag (positiveGL a b c)) = 2)
    ) := by
  refine ⟨matrixWord_permutation (K := K), ?_⟩
  exact ⟨decreasing_character_rank, positive_character_rank,
    SchubertOrbits.deodhar_product_decreasing,
    SchubertOrbits.deodhar_product_positive,
    rootCharacter_matrixRoot 3 0 1 (by decide),
    rootCharacter_matrixRoot 3 1 2 (by decide),
    matrixWord_reduced,
    decreasing_distinguished,
    positive_distinguished,
    positive_isPositive,
    identity_expressions,
    decreasing_standard_matrices,
    positive_standard_matrices,
    decreasing_character1,
    decreasing_character2,
    positive_character,
    decreasing_rank,
    positive_rank,
    decreasing_scheme_action,
    positive_scheme_action,
    action_admissible,
    decreasing_matrix_flag_rank,
    positive_matrix_flag_rank⟩

end SchubertOrbits
