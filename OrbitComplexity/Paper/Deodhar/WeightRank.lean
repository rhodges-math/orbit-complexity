import OrbitComplexity.Paper.Deodhar.RootIndices
import OrbitComplexity.Paper.Deodhar.Characters

/-!
# Character ranks of subexpressions

Each omitted or decreasing position contributes the character of its negative signed root.
The real span of these torus characters has the dimension of the subexpression's root span.

## Main definitions and results

* `subwordCharacter`: the negative signed-root character at a selected position.
* `subwordCharacter_rank`: equality of character-span rank and subexpression weight dimension.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  Definition 3.19 and Theorem 1.4.
-/

namespace SchubertOrbits

open BruhatIntervals

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- The torus character of the negative signed root at an omitted or decreasing position. -/
def subwordCharacter (j : {position : Fin word.length //
    position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}) : G.characters :=
  let r := subwordRootIndex G.rootBase expression j.val
  G.rootCharacter (G.rootSystem.reflectionPerm r r)

set_option maxHeartbeats 400000 in
/-- The selected negative-root characters and subexpression roots have equal real span dimension. -/
theorem subwordCharacter_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (j : {position : Fin word.length //
          position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
            negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression})
        (k : G.torusIndex) => ((subwordCharacter G expression j).toAdd k : ℝ)))) =
      subwordWeightDim (weylRealization G.rootBase) expression := by
  have hneg (j : Fin word.length) : normalizedRoot G.rootBase
      (G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j)
        (subwordRootIndex G.rootBase expression j)) =
      -subwordRoot (weylRealization G.rootBase) expression j :=
    (normalizedRoot_neg G.rootBase _).trans
      (congrArg Neg.neg (subwordRoot_eq_normalized G.rootBase expression j).symm)
  have hroots : Set.range
      (fun j : {position : Fin word.length //
          position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
            negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} =>
        normalizedRoot G.rootBase (G.rootSystem.reflectionPerm
          (subwordRootIndex G.rootBase expression j.val)
          (subwordRootIndex G.rootBase expression j.val))) =
      (fun j => -subwordRoot (weylRealization G.rootBase) expression j) ''
        (equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) := by
    ext vector
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j.val, j.property, ?_⟩
      exact (hneg j.val).symm
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j, hj⟩, ?_⟩
      exact hneg j
  have hrank := rootCharacter_root_rank G
    (fun j : {position : Fin word.length //
        position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} =>
      G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j.val)
        (subwordRootIndex G.rootBase expression j.val))
  have hspan := (congrArg (Submodule.span ℝ) hroots).trans
    (subwordWeightSpan_eq_neg (weylRealization G.rootBase) expression).symm
  have hdimension := congrArg
    (fun space : Submodule ℝ (G.rootBase.support →₀ ℝ) => Module.finrank ℝ space) hspan
  exact hrank.trans hdimension

end
end SchubertOrbits
