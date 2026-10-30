import OrbitComplexity.Paper.Deodhar.Realization
import OrbitComplexity.Paper.Deodhar.Roots

/-! # Root indices of subexpressions

Signed prefix roots are represented by normalized vectors of the root datum.
-/

open scoped TensorProduct

namespace SchubertOrbits
noncomputable section
open BruhatIntervals
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Fintype ι] [P.IsCrystallographic] (b : P.Base)

/-- Negating the root index negates its normalized real coordinate vector. -/
theorem normalizedRoot_neg (r : ι) :
    normalizedRoot b (P.reflectionPerm r r) = -normalizedRoot b r := by
  simp only [normalizedRoot, RootPairing.RootPositiveForm.rootLength_reflectionPerm_self,
    realRoot, RootPairing.rootSpanMem_reflectionPerm_self, TensorProduct.tmul_neg,
    map_neg, smul_neg]

variable [P.IsReduced] {word : List b.support} (expression : Subexpression word)

/-- The root index attached to a subexpression position uses the signed prefix root. -/
def subwordRootIndex (j : Fin word.length) : ι := by
  classical
  let r := P.weylGroupToPerm (expression.prefixProd (ReductiveGroups.weylCoxeterSystem b)
    j.val) (word[j.val] : ι)
  exact if j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem b) expression then
    P.reflectionPerm r r else r

/-- The geometric subexpression root is the normalized vector of its root index. -/
theorem subwordRoot_eq_normalized (j : Fin word.length) :
    subwordRoot (weylRealization b) expression j =
      normalizedRoot b (subwordRootIndex b expression j) := by
  classical
  have hact : (weylRealization b).action
      (expression.prefixProd (ReductiveGroups.weylCoxeterSystem b) j.val)
      ((weylRealization b).simpleRoot word[j.val]) =
      normalizedRoot b (P.weylGroupToPerm
        (expression.prefixProd (ReductiveGroups.weylCoxeterSystem b) j.val)
        (word[j.val] : ι)) := by
    change rootCoordinateAction b _ (BruhatIntervals.normalizedSimpleRoot b _) = _
    rw [← normalizedRoot_simple, rootCoordinateAction_normalized]
  by_cases hj : j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem b) expression
  · rw [subwordRoot_of_negative _ _ j hj, hact]
    simp only [subwordRootIndex, ite_eq_left hj, normalizedRoot_neg]
  · rw [subwordRoot, ite_eq_right hj, hact]
    simp only [subwordRootIndex, ite_eq_right hj]

end
end SchubertOrbits
