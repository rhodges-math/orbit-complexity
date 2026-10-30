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

/-! # Identity subexpressions in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The reduced word s₁s₂s₁ in the general-linear Weyl group of rank three. -/
def matrixWord : List (GLn.groupData K 3).rootBase.support := [simple01, simple12, simple01]

/-- The word s₁s₂s₁ is reduced. -/
theorem matrixWord_reduced :
    (weylCoxeterSystem (GLn.groupData K 3).rootBase).IsReduced matrixWord := by
  let G := GLn.groupData K 3
  let s := RootPairing.weylGroup.ofIdx G.rootSystem root01
  let t := RootPairing.weylGroup.ofIdx G.rootSystem root12
  have h1 : rootInversionCount G.rootBase s = 1 := by
    simpa only [s, simple01, one_mul, rootInversionCount_one, zero_add] using
      rootInversionCount_mul_simple_of_pos G.rootBase 1 simple01
        (by simpa only [map_one, Equiv.Perm.one_apply, simple01] using
          G.rootBase.isPos_of_mem_support root01_simple)
  have h2 : rootInversionCount G.rootBase (s * t) = 2 := by
    have hp : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm s root12) := by
      rw [weylGroupToPerm_simple, reflection01_root12]
      exact (matrixRoot_positive 3 0 2 (by decide)).mpr (by decide)
    simpa only [h1, t, simple12] using rootInversionCount_mul_simple_of_pos G.rootBase s simple12 hp
  have h3 : rootInversionCount G.rootBase ((s * t) * s) = 3 := by
    have hp : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (s * t) root01) := by
      rw [map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple,
        weylGroupToPerm_simple, reflection12_root01, reflection01_root02]
      exact G.rootBase.isPos_of_mem_support root12_simple
    simpa only [h2, s, simple01] using rootInversionCount_mul_simple_of_pos G.rootBase (s * t)
      simple01 hp
  rw [weylCoxeterSystem_isReduced_iff]
  simpa only [s, t, simple01, simple12, matrixWord, simpleWeylWord, List.map_cons, List.map_nil,
    List.prod_cons,
    List.prod_nil, mul_one, List.length_cons, List.length_nil, mul_assoc] using h3

private theorem identity121 {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i j : S)
    (h12 : cs.length (cs.simple i * cs.simple j) = 2)
    (h21 : cs.length (cs.simple j * cs.simple i) = 2)
    (h121 : cs.length (cs.simple i * (cs.simple j * cs.simple i)) = 3)
    (expression : BruhatIntervals.Subexpression [i, j, i]) :
    expression.prefixProd cs 3 = 1 ↔
      expression = ⟨[true, false, true], rfl⟩ ∨
      expression = ⟨[false, false, false], rfl⟩ := by
  constructor
  · intro hf
    rcases expression with ⟨choices, hchoices⟩
    change choices.length = 3 at hchoices
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hchoices
    cases a <;> cases b <;> cases c
    all_goals
      first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | have hh := congrArg cs.length hf
        simp only [BruhatIntervals.Subexpression.prefixProd,
          BruhatIntervals.Subexpression.factors, List.zip_cons_cons,
          List.zip_nil_left, List.map_cons, List.map_nil, List.take_succ_cons,
          List.take_zero, List.prod_cons, List.prod_nil, Bool.false_eq_true,
          ↓reduceIte, one_mul, mul_one] at hh
        norm_num only [h12, h21, h121, cs.length_simple, cs.length_one] at hh
  · rintro (rfl | rfl) <;>
      simp [BruhatIntervals.Subexpression.prefixProd,
        BruhatIntervals.Subexpression.factors, cs.simple_mul_simple_self]

private theorem allfalse_distinguished {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i j : S) :
    BruhatIntervals.IsDistinguished cs
      (⟨[false, false, false], rfl⟩ : BruhatIntervals.Subexpression [i, j, i]) := by
  intro n
  fin_cases n <;>
    simp [BruhatIntervals.Subexpression.prefixProd, BruhatIntervals.Subexpression.factors]

/-- The subexpression selecting no simple reflection is positive. -/
theorem allfalse_positive {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i j : S) :
    BruhatIntervals.IsPositive cs
      (⟨[false, false, false], rfl⟩ : BruhatIntervals.Subexpression [i, j, i]) := by
  intro n
  fin_cases n <;>
    simp [BruhatIntervals.Subexpression.prefixProd, BruhatIntervals.Subexpression.factors]

/-- The prefixes of the subexpression s₁1s₁ are computed in order. -/
theorem decreasing_prefix {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i j : S) (n : Fin 4) :
    (⟨[true, false, true], rfl⟩ : BruhatIntervals.Subexpression [i, j, i]).prefixProd cs n.val =
      (![1, cs.simple i, cs.simple i, 1] : Fin 4 → W) n := by
  fin_cases n <;>
    simp [BruhatIntervals.Subexpression.prefixProd, BruhatIntervals.Subexpression.factors]

/-- The subexpression s₁1s₁ of s₁s₂s₁. -/
def decreasingExpression : BruhatIntervals.Subexpression (matrixWord (K := K)) :=
  ⟨[true, false, true], rfl⟩

/-- The subexpression 111 of s₁s₂s₁. -/
def positiveExpression : BruhatIntervals.Subexpression (matrixWord (K := K)) :=
  ⟨[false, false, false], rfl⟩

open BruhatIntervals

private theorem matrixWord_length12 :
    (weylCoxeterSystem (GLn.groupData K 3).rootBase).length
      ((weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple01 *
        (weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple12) = 2 := by
  have h := (matrixWord_reduced (K := K)).take 2
  simpa only [matrixWord, CoxeterSystem.IsReduced, CoxeterSystem.wordProd,
    List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.length_cons, List.length_nil] using h

private theorem matrixWord_length21 :
    (weylCoxeterSystem (GLn.groupData K 3).rootBase).length
      ((weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple12 *
        (weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple01) = 2 := by
  have h := (matrixWord_reduced (K := K)).drop 1
  simpa only [matrixWord, CoxeterSystem.IsReduced, CoxeterSystem.wordProd,
    List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.length_cons, List.length_nil] using h

private theorem matrixWord_length121 :
    (weylCoxeterSystem (GLn.groupData K 3).rootBase).length
      ((weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple01 *
        ((weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple12 *
          (weylCoxeterSystem (GLn.groupData K 3).rootBase).simple simple01)) = 3 := by
  simpa only [matrixWord, CoxeterSystem.IsReduced, CoxeterSystem.wordProd,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil] using matrixWord_reduced (K := K)

/-- Exactly s₁1s₁ and 111 evaluate to the identity in the word s₁s₂s₁. -/
theorem identity_expressions (expression : Subexpression (matrixWord (K := K))) :
    expression.prefixProd (weylCoxeterSystem (GLn.groupData K 3).rootBase) 3 = 1 ↔
      expression = decreasingExpression ∨ expression = positiveExpression :=
  identity121 _ simple01 simple12 matrixWord_length12 matrixWord_length21
    matrixWord_length121 expression

/-- The subexpression s₁1s₁ is distinguished. -/
theorem decreasing_distinguished :
    IsDistinguished (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (decreasingExpression (K := K)) := by
  let cs := weylCoxeterSystem (GLn.groupData K 3).rootBase
  apply (isDistinguished_iff_forced cs _).mpr
  intro j hj
  fin_cases j
  · rfl
  · have hbad : cs.length (cs.simple simple01 * cs.simple simple12) <
        cs.length (cs.simple simple01) := by
      simpa [CoxeterSystem.IsRightDescent, Subexpression.prefixProd, Subexpression.factors,
        decreasingExpression, matrixWord] using hj
    rw [matrixWord_length12, cs.length_simple] at hbad
    omega
  · rfl

/-- The subexpression 111 is distinguished. -/
theorem positive_distinguished :
    IsDistinguished (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K)) :=
  allfalse_distinguished _ simple01 simple12

/-- The subexpression 111 is positive. -/
theorem positive_isPositive :
    IsPositive (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K)) :=
  allfalse_positive _ simple01 simple12

/-- The middle position is the only equal step of s₁1s₁. -/
theorem decreasing_equal :
    equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (decreasingExpression (K := K)) = {⟨1, by change 1 < 3; decide⟩} := by
  let cs := weylCoxeterSystem (GLn.groupData K 3).rootBase
  have hs : cs.simple simple01 ≠ 1 := by
    intro h
    have hl := cs.length_simple simple01
    rw [h, cs.length_one] at hl
    omega
  have hp (n : Fin 4) : decreasingExpression.prefixProd cs n.val =
      (![1, cs.simple simple01, cs.simple simple01, 1] :
        Fin 4 → (GLn.groupData K 3).weylGroup) n :=
    decreasing_prefix cs simple01 simple12 n
  have h0 : decreasingExpression.prefixProd cs 0 = 1 := hp (0 : Fin 4)
  have h1 : decreasingExpression.prefixProd cs 1 = cs.simple simple01 := hp (1 : Fin 4)
  have h2 : decreasingExpression.prefixProd cs 2 = cs.simple simple01 := hp (2 : Fin 4)
  have h3 : decreasingExpression.prefixProd cs 3 = 1 := hp (3 : Fin 4)
  apply Set.ext (fun j : Fin 3 => ?_)
  change (decreasingExpression.prefixProd cs j.val =
    decreasingExpression.prefixProd cs (j.val + 1)) ↔ j = (1 : Fin 3)
  fin_cases j
  · change (decreasingExpression.prefixProd cs 0 = decreasingExpression.prefixProd cs 1) ↔
      (0 : Fin 3) = 1
    rw [h0, h1]
    exact iff_of_false hs.symm (by decide)
  · change (decreasingExpression.prefixProd cs 1 = decreasingExpression.prefixProd cs 2) ↔
      (1 : Fin 3) = 1
    rw [h1, h2]
    exact iff_of_true rfl rfl
  · change (decreasingExpression.prefixProd cs 2 = decreasingExpression.prefixProd cs 3) ↔
      (2 : Fin 3) = 1
    rw [h2, h3]
    exact iff_of_false hs (by decide)

private theorem decreasing_negative_steps {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i j : S) :
    negativeSteps cs (⟨[true, false, true], rfl⟩ : Subexpression [i, j, i]) =
      {⟨2, by change 2 < 3; decide⟩} := by
  let expression : Subexpression [i, j, i] := ⟨[true, false, true], rfl⟩
  have hs : cs.simple i ≠ 1 := by
    intro h
    have hl := cs.length_simple i
    rw [h, cs.length_one] at hl
    omega
  have hp (n : Fin 4) : expression.prefixProd cs n.val =
      (![1, cs.simple i, cs.simple i, 1] :
        Fin 4 → W) n :=
    decreasing_prefix cs i j n
  have h0 : expression.prefixProd cs 0 = 1 := hp (0 : Fin 4)
  have h1 : expression.prefixProd cs 1 = cs.simple i := hp (1 : Fin 4)
  have h2 : expression.prefixProd cs 2 = cs.simple i := hp (2 : Fin 4)
  have h3 : expression.prefixProd cs 3 = 1 := hp (3 : Fin 4)
  apply Set.ext (fun j : Fin 3 => ?_)
  change (cs.BruhatLE (expression.prefixProd cs (j.val + 1))
      (expression.prefixProd cs j.val) ∧
    expression.prefixProd cs (j.val + 1) ≠
      expression.prefixProd cs j.val) ↔ j = (2 : Fin 3)
  fin_cases j
  · change (cs.BruhatLE (expression.prefixProd cs 1)
        (expression.prefixProd cs 0) ∧ expression.prefixProd cs 1 ≠
        expression.prefixProd cs 0) ↔ (0 : Fin 3) = 2
    rw [h1, h0]
    apply iff_of_false ?_ (by decide)
    rintro ⟨hle, hne⟩
    exact hne (cs.bruhatLE_one_iff.mp hle)
  · change (cs.BruhatLE (expression.prefixProd cs 2)
        (expression.prefixProd cs 1) ∧ expression.prefixProd cs 2 ≠
        expression.prefixProd cs 1) ↔ (1 : Fin 3) = 2
    rw [h2, h1]
    exact iff_of_false (fun h => h.2 rfl) (by decide)
  · change (cs.BruhatLE (expression.prefixProd cs 3)
        (expression.prefixProd cs 2) ∧ expression.prefixProd cs 3 ≠
        expression.prefixProd cs 2) ↔ (2 : Fin 3) = 2
    rw [h3, h2]
    exact iff_of_true ⟨cs.one_bruhatLE _, hs.symm⟩ rfl

/-- The last position is the only decreasing step of s₁1s₁. -/
theorem decreasing_negative :
    negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (decreasingExpression (K := K)) = {⟨2, by change 2 < 3; decide⟩} :=
  decreasing_negative_steps _ simple01 simple12

/-- Every position is an equal step of 111. -/
theorem positive_equal :
    equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K)) = Set.univ := by
  apply Set.ext (fun j : Fin 3 => ?_)
  constructor
  · intro _
    trivial
  · intro _
    fin_cases j <;> rfl

/-- The subexpression 111 has no decreasing steps. -/
theorem positive_negative :
    negativeSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      (positiveExpression (K := K)) = ∅ :=
  (isPositive_iff_negativeSteps_empty _ _).mp positive_isPositive

/-- The length of the word s₁s₂s₁ is nonzero. -/
theorem matrixWord_neZero : NeZero (matrixWord (K := K)).length :=
  ⟨by change (3 : ℕ) ≠ 0; decide⟩

end SchubertOrbits.GL3
