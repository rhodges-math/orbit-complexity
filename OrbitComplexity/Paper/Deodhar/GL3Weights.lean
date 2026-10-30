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

/-! # Characters of rank-three Deodhar parameters -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The middle selected position of s₁1s₁. -/
def decreasingJ1 : {j : Fin (matrixWord (K := K)).length //
    j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) decreasingExpression ∪
      negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) decreasingExpression} :=
  ⟨⟨1, by change 1 < 3; decide⟩, Or.inl (by rw [decreasing_equal]; rfl)⟩

/-- The final selected position of s₁1s₁. -/
def decreasingJ2 : {j : Fin (matrixWord (K := K)).length //
    j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) decreasingExpression ∪
      negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) decreasingExpression} :=
  ⟨⟨2, by change 2 < 3; decide⟩, Or.inr (by rw [decreasing_negative]; rfl)⟩

/-- A position of 111 viewed as a selected position. -/
def positiveJ (i : Fin 3) : {j : Fin (matrixWord (K := K)).length //
    j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) positiveExpression ∪
      negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) positiveExpression} :=
  ⟨i, Or.inl (by rw [positive_equal]; trivial)⟩

private theorem rootIndex_of_not_negative (G : ReductiveGroupData K)
    {word : List G.rootBase.support} (e : Subexpression word) (j : Fin word.length)
    (hn : j ∉ negativeSteps (weylCoxeterSystem G.rootBase) e) :
    SchubertOrbits.subwordRootIndex G.rootBase e j =
      G.rootSystem.weylGroupToPerm (e.prefixProd (weylCoxeterSystem G.rootBase) j.val)
        word[j.val].val := by
  unfold SchubertOrbits.subwordRootIndex
  exact ite_eq_right hn

private theorem rootIndex_of_negative (G : ReductiveGroupData K)
    {word : List G.rootBase.support} (e : Subexpression word) (j : Fin word.length)
    (hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) e) :
    SchubertOrbits.subwordRootIndex G.rootBase e j =
      let r : G.rootIndex := G.rootSystem.weylGroupToPerm
        (e.prefixProd (weylCoxeterSystem G.rootBase) j.val) word[j.val].val
      G.rootSystem.reflectionPerm r r := by
  unfold SchubertOrbits.subwordRootIndex
  exact ite_eq_left hn

private theorem decreasing_rootIndex1 :
    SchubertOrbits.subwordRootIndex (GLn.groupData K 3).rootBase decreasingExpression
      decreasingJ1.val = root02 := by
  let G := GLn.groupData K 3
  let cs := weylCoxeterSystem G.rootBase
  have hn : (decreasingJ1 (K := K)).val ∉ negativeSteps cs decreasingExpression := by
    change (1 : Fin 3) ∉ negativeSteps cs decreasingExpression
    rw [decreasing_negative]
    change (1 : Fin 3) ≠ 2
    decide
  have hp : (decreasingExpression (K := K)).prefixProd cs 1 = cs.simple simple01 :=
    decreasing_prefix cs simple01 simple12 (1 : Fin 4)
  calc
    SchubertOrbits.subwordRootIndex G.rootBase decreasingExpression decreasingJ1.val =
        G.rootSystem.weylGroupToPerm (decreasingExpression.prefixProd cs 1) root12 :=
      rootIndex_of_not_negative G decreasingExpression decreasingJ1.val hn
    _ = root02 := by
      rw [hp, weylCoxeterSystem_simple, weylGroupToPerm_simple]
      exact reflection01_root12

private theorem rootSelf_involution (r : (GLn.groupData K 3).rootIndex) :
    (GLn.groupData K 3).rootSystem.reflectionPerm
      ((GLn.groupData K 3).rootSystem.reflectionPerm r r)
      ((GLn.groupData K 3).rootSystem.reflectionPerm r r) = r := by
  let := (GLn.groupData K 3).rootSystem.indexNeg
  exact neg_neg r

private theorem decreasing_rootIndex2 :
    SchubertOrbits.subwordRootIndex (GLn.groupData K 3).rootBase decreasingExpression
      decreasingJ2.val = root01 := by
  let G := GLn.groupData K 3
  let cs := weylCoxeterSystem G.rootBase
  have hn : (decreasingJ2 (K := K)).val ∈ negativeSteps cs decreasingExpression := by
    change (2 : Fin 3) ∈ negativeSteps cs decreasingExpression
    rw [decreasing_negative]
    rfl
  have hp : (decreasingExpression (K := K)).prefixProd cs 2 = cs.simple simple01 :=
    decreasing_prefix cs simple01 simple12 (2 : Fin 4)
  let r : G.rootIndex := G.rootSystem.weylGroupToPerm
    (decreasingExpression.prefixProd cs 2) root01
  have hr : r = G.rootSystem.reflectionPerm root01 root01 := by
    change G.rootSystem.weylGroupToPerm
      (decreasingExpression.prefixProd cs 2) root01 = _
    rw [hp, weylCoxeterSystem_simple, weylGroupToPerm_simple]
    rfl
  have hi : SchubertOrbits.subwordRootIndex G.rootBase decreasingExpression decreasingJ2.val =
      G.rootSystem.reflectionPerm r r :=
    rootIndex_of_negative G decreasingExpression decreasingJ2.val hn
  exact hi.trans ((congrArg (fun t => G.rootSystem.reflectionPerm t t) hr).trans
    (rootSelf_involution root01))

private theorem allfalse_rootIndex (G : ReductiveGroupData K)
    (i j : G.rootBase.support) (q : Fin 3) :
    SchubertOrbits.subwordRootIndex G.rootBase
      (⟨[false, false, false], rfl⟩ : Subexpression [i, j, i]) q =
        (![i.val, j.val, i.val] : Fin 3 → G.rootIndex) q := by
  let cs := weylCoxeterSystem G.rootBase
  let e : Subexpression [i, j, i] := ⟨[false, false, false], rfl⟩
  have hn : q ∉ negativeSteps cs e := by
    have he : negativeSteps cs e = ∅ :=
      (isPositive_iff_negativeSteps_empty cs e).mp (allfalse_positive cs i j)
    intro hq
    exact (Set.ext_iff.mp he q).mp hq
  have hp : e.prefixProd cs q.val = 1 := by
    fin_cases q <;> simp [e, Subexpression.prefixProd, Subexpression.factors]
  have he := rootIndex_of_not_negative G e q hn
  rw [hp, map_one] at he
  refine he.trans ?_
  fin_cases q <;> rfl

private theorem positive_rootIndex (j : Fin 3) :
    SchubertOrbits.subwordRootIndex (GLn.groupData K 3).rootBase positiveExpression
      (positiveJ j).val = (![root01, root12, root01] : Fin 3 → (GLn.groupData K 3).rootIndex) j :=
  allfalse_rootIndex (GLn.groupData K 3) simple01 simple12 j

/-- The middle parameter of s₁1s₁ has character t₂t₀⁻¹. -/
theorem decreasing_character1 :
    SchubertOrbits.subwordCharacter (GLn.groupData K 3) decreasingExpression
      decreasingJ1 = matrixUnitWeight 2 0 := by
  simp only [SchubertOrbits.subwordCharacter, decreasing_rootIndex1]
  change (GLn.groupData K 3).rootCharacter
    ((GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 0 2 (by decide))
      (matrixRoot 3 0 2 (by decide))) = _
  rw [matrixRoot_swap, rootCharacter_matrixRoot]

/-- The last parameter of s₁1s₁ has character t₁t₀⁻¹. -/
theorem decreasing_character2 :
    SchubertOrbits.subwordCharacter (GLn.groupData K 3) decreasingExpression
      decreasingJ2 = matrixUnitWeight 1 0 := by
  simp only [SchubertOrbits.subwordCharacter, decreasing_rootIndex2]
  change (GLn.groupData K 3).rootCharacter
    ((GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 0 1 (by decide))
      (matrixRoot 3 0 1 (by decide))) = _
  rw [matrixRoot_swap, rootCharacter_matrixRoot]

/-- The three parameters of 111 have characters t₁t₀⁻¹, t₂t₁⁻¹, t₁t₀⁻¹. -/
theorem positive_character (j : Fin 3) :
    SchubertOrbits.subwordCharacter (GLn.groupData K 3) positiveExpression
      (positiveJ j) =
        (![matrixUnitWeight 1 0, matrixUnitWeight 2 1, matrixUnitWeight 1 0] :
          Fin 3 → (GLn.groupData K 3).characters) j := by
  simp only [SchubertOrbits.subwordCharacter, positive_rootIndex]
  fin_cases j
  · change (GLn.groupData K 3).rootCharacter
      ((GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 0 1 (by decide))
        (matrixRoot 3 0 1 (by decide))) = matrixUnitWeight 1 0
    rw [matrixRoot_swap, rootCharacter_matrixRoot]
  · change (GLn.groupData K 3).rootCharacter
      ((GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 1 2 (by decide))
        (matrixRoot 3 1 2 (by decide))) = matrixUnitWeight 2 1
    rw [matrixRoot_swap, rootCharacter_matrixRoot]
  · change (GLn.groupData K 3).rootCharacter
      ((GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 0 1 (by decide))
        (matrixRoot 3 0 1 (by decide))) = matrixUnitWeight 1 0
    rw [matrixRoot_swap, rootCharacter_matrixRoot]

end SchubertOrbits.GL3
