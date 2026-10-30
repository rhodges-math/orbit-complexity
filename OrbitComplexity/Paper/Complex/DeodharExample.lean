import OrbitComplexity.Paper.Deodhar.RankThreeExample

/-! # Complex rank-three Deodhar component example -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals SchubertOrbits.GL3
open scoped Classical

noncomputable section
namespace SchubertOrbits

/-- The rank-three Weyl permutations, component matrices, weights and torus orbits over ℂ. -/
theorem deodhar_example_complex :
  (
      ∃ e : (GLn.groupData ℂ 3).weylGroup ≃* Equiv.Perm (Fin 3),
        e (RootPairing.weylGroup.ofIdx (GLn.groupData ℂ 3).rootSystem root01) =
          Equiv.swap 0 1 ∧
        e (RootPairing.weylGroup.ofIdx (GLn.groupData ℂ 3).rootSystem root12) =
          Equiv.swap 1 2 ∧
        e (simpleWeylWord (GLn.groupData ℂ 3).rootBase matrixWord) = Equiv.swap 0 2 ∧
        (∀ i : Fin 3, e (simpleWeylWord (GLn.groupData ℂ 3).rootBase matrixWord) i =
          (![2, 1, 0] : Fin 3 → Fin 3) i) ∧
        (∀ i : Fin 3, e 1 i = (![0, 1, 2] : Fin 3 → Fin 3) i) ∧
        simpleWeylWord (GLn.groupData ℂ 3).rootBase matrixWord =
          (GLn.groupData ℂ 3).longestElement
      ) ∧ (
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (parameterWeight (K := ℂ) decreasingExpression))) = 2) ∧
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (parameterWeight (K := ℂ) positiveExpression))) = 2) ∧
      (∀ parameter coordinate : ℂ,
      (!![0, -1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℂ) *
        !![1, 0, 0; 0, 1, 0; 0, parameter, 1] *
        (!![1, coordinate, 0; 0, 1, 0; 0, 0, 1] * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) =
          !![1, 0, 0; -coordinate, 1, 0; -parameter, 0, 1]) ∧
      (∀ first second third : ℂ,
      (!![1, 0, 0; first, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℂ) *
        !![1, 0, 0; 0, 1, 0; 0, second, 1] * !![1, 0, 0; third, 1, 0; 0, 0, 1] =
          !![1, 0, 0; first + third, 1, 0; second * third, second, 1]) ∧
      ((GLn.groupData ℂ 3).rootCharacter (simple01 (K := ℂ)).val = matrixUnitWeight 0 1) ∧
      ((GLn.groupData ℂ 3).rootCharacter (simple12 (K := ℂ)).val = matrixUnitWeight 1 2) ∧
      ((weylCoxeterSystem (GLn.groupData ℂ 3).rootBase).IsReduced matrixWord) ∧
      (IsDistinguished (weylCoxeterSystem (GLn.groupData ℂ 3).rootBase)
        (decreasingExpression (K := ℂ))) ∧
      (IsDistinguished (weylCoxeterSystem (GLn.groupData ℂ 3).rootBase)
        (positiveExpression (K := ℂ))) ∧
      (IsPositive (weylCoxeterSystem (GLn.groupData ℂ 3).rootBase)
        (positiveExpression (K := ℂ))) ∧
      (∀ expression : Subexpression (matrixWord (K := ℂ)),
      expression.prefixProd (weylCoxeterSystem (GLn.groupData ℂ 3).rootBase) 3 = 1 ↔
        expression = decreasingExpression ∨ expression = positiveExpression) ∧
      (Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData ℂ 3)
        decreasingExpression matrixWord_reduced decreasing_distinguished).points =>
        (matrixPoints (K := ℂ) ((GroupActions.reductivePointsEquiv (GLn.groupData ℂ 3)).symm
          (GroupActions.Variety.mapPoints
            (X := SchubertGeometry.deodharStandardVariety (GLn.groupData ℂ 3) decreasingExpression
              matrixWord_reduced decreasing_distinguished)
            (Y := GroupActions.reductiveVariety (GLn.groupData ℂ 3))
            (SchubertGeometry.deodharStandardInclusion (GLn.groupData ℂ 3) decreasingExpression
              matrixWord_reduced decreasing_distinguished) x)) : Matrix (Fin 3) (Fin 3) ℂ)) =
        {M | ∃ p m : ℂ, p ≠ 0 ∧ decreasingMatrix p m = M}) ∧
      (Set.range (fun x : (SchubertGeometry.deodharStandardVariety (GLn.groupData ℂ 3)
        positiveExpression matrixWord_reduced positive_distinguished).points =>
        (matrixPoints (K := ℂ) ((GroupActions.reductivePointsEquiv (GLn.groupData ℂ 3)).symm
          (GroupActions.Variety.mapPoints
            (X := SchubertGeometry.deodharStandardVariety (GLn.groupData ℂ 3) positiveExpression
              matrixWord_reduced positive_distinguished)
            (Y := GroupActions.reductiveVariety (GLn.groupData ℂ 3))
            (SchubertGeometry.deodharStandardInclusion (GLn.groupData ℂ 3) positiveExpression
              matrixWord_reduced positive_distinguished) x)) : Matrix (Fin 3) (Fin 3) ℂ)) =
        {M | ∃ a b c : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ positiveMatrix a b c = M}) ∧
      (SchubertOrbits.subwordCharacter (GLn.groupData ℂ 3) decreasingExpression
        decreasingJ1 = matrixUnitWeight 2 0) ∧
      (SchubertOrbits.subwordCharacter (GLn.groupData ℂ 3) decreasingExpression
        decreasingJ2 = matrixUnitWeight 1 0) ∧
      (∀ j : Fin 3,
      SchubertOrbits.subwordCharacter (GLn.groupData ℂ 3) positiveExpression
        (positiveJ j) =
          (![matrixUnitWeight 1 0, matrixUnitWeight 2 1, matrixUnitWeight 1 0] :
            Fin 3 → (GLn.groupData ℂ 3).characters) j) ∧
      (Module.finrank ℝ (Submodule.span ℝ (Set.range decreasingWeights)) = 2) ∧
      (Module.finrank ℝ (Submodule.span ℝ (Set.range positiveWeights)) = 2) ∧
      (∀ (t : Fin 3 → ℂˣ) (p m : ℂ),
      schemeDiagonalPoint t • schemeMatrixFlag (decreasingGL p m) =
        schemeMatrixFlag (decreasingGL ((t 2 : ℂ) / t 0 * p) ((t 1 : ℂ) / t 0 * m))) ∧
      (∀ (t : Fin 3 → ℂˣ) (a b c : ℂ),
      schemeDiagonalPoint t • schemeMatrixFlag (positiveGL a b c) =
        schemeMatrixFlag (positiveGL ((t 1 : ℂ) / t 0 * a) ((t 2 : ℂ) / t 1 * b)
          ((t 1 : ℂ) / t 0 * c))) ∧
      (∀ (t : Fin 3 → ℂˣ) (p m a b c : ℂ),
      p ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      (t 2 : ℂ) / t 0 * p ≠ 0 ∧
      (((t 1 : ℂ) / t 0 * m ≠ 0) ↔ m ≠ 0) ∧
      (t 1 : ℂ) / t 0 * a ≠ 0 ∧ (t 2 : ℂ) / t 1 * b ≠ 0 ∧
      (t 1 : ℂ) / t 0 * c ≠ 0) ∧
      (∀ (p m : ℂ), p ≠ 0 →
      orbitNatDim (torusVariety (GLn.groupData ℂ 3)) (flagVariety (GLn.groupData ℂ 3))
        (schemeMatrixFlag (decreasingGL p m)) = if m = 0 then 1 else 2) ∧
      (∀ (a b c : ℂ), a ≠ 0 → b ≠ 0 → c ≠ 0 →
      orbitNatDim (torusVariety (GLn.groupData ℂ 3)) (flagVariety (GLn.groupData ℂ 3))
        (schemeMatrixFlag (positiveGL a b c)) = 2)
      ) :=
  deodhar_example (K := ℂ)

end SchubertOrbits
