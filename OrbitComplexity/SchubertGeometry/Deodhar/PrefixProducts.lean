import OrbitComplexity.SchubertGeometry.Deodhar.Products
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterPrefixes
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterMaps

/-! # Products of truncated subexpressions

Truncation retains each signed factor and selected root coordinate up to its endpoint.
The regular flag morphisms therefore commute with the parameter projection to a prefix.
-/

open CategoryTheory BruhatIntervals ReductiveGroups GroupActions GroupActions.Variety
open SchubertGeometry
namespace SchubertGeometry
noncomputable section

private theorem ofFn_restrict {S A : Type*} (word : List S) (f : Fin word.length → A)
    (n : ℕ) :
    List.ofFn (fun j : Fin (word.take n).length => f (Subexpression.takePosition n j)) =
      (List.ofFn f).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take]
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_take, Subexpression.takePosition]

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem step_take (n : ℕ) (j : Fin (word.take n).length) :
    subwordStepPoint G (expression.take n) j =
      subwordStepPoint G expression (Subexpression.takePosition n j) := by
  classical
  simp only [subwordStepPoint, expression.negativeSteps_take (weylCoxeterSystem G.rootBase),
    expression.equalSteps_take (weylCoxeterSystem G.rootBase), List.getElem_take,
    Subexpression.takePosition]
  rfl

private theorem root_take (parameters : Fin word.length → K) (n : ℕ)
    (j : Fin (word.take n).length) :
    deodharRootElement G (expression.take n)
      (fun j => parameters (Subexpression.takePosition n j)) j =
        deodharRootElement G expression parameters (Subexpression.takePosition n j) := by
  classical
  simp only [deodharRootElement,
    expression.negativeSteps_take (weylCoxeterSystem G.rootBase),
    expression.equalSteps_take (weylCoxeterSystem G.rootBase), List.getElem_take,
    Subexpression.takePosition]
  rfl

private theorem factor_take (parameters : Fin word.length → K) (n : ℕ)
    (j : Fin (word.take n).length) :
    deodharStep G (expression.take n)
      (fun j => parameters (Subexpression.takePosition n j)) j =
        deodharStep G expression parameters (Subexpression.takePosition n j) := by
  exact congrArg₂ (fun a b : G.points => a * b)
    (root_take G expression parameters n j) (step_take G expression n j)

/-- Signed representatives of truncated words are the corresponding original prefixes. -/
theorem subwordRepresentative_take (n k : ℕ) :
    subwordRepresentative G (expression.take n) k =
      subwordRepresentative G expression (min k n) := by
  have h : subwordStepPoint G (expression.take n) =
      fun j => subwordStepPoint G expression (Subexpression.takePosition n j) :=
    funext (step_take G expression n)
  simp only [subwordRepresentative, h, ofFn_restrict, List.take_take, Nat.min_comm]

/-- The Deodhar product of a truncated subexpression is the original prefix product. -/
theorem deodharPrefix_take (parameters : Fin word.length → K) (n k : ℕ) :
    deodharPrefix G (expression.take n)
      (fun j => parameters (Subexpression.takePosition n j)) k =
        deodharPrefix G expression parameters (min k n) := by
  have h : deodharStep G (expression.take n)
      (fun j => parameters (Subexpression.takePosition n j)) =
        fun j => deodharStep G expression parameters (Subexpression.takePosition n j) :=
    funext (factor_take G expression parameters n)
  simp only [deodharPrefix, h, ofFn_restrict, List.take_take, Nat.min_comm]

private theorem rootProduct_take_raw (parameters : Fin word.length → K) (n k : ℕ) :
    subwordRootProduct G (expression.take n)
      (fun j => parameters (Subexpression.takePosition n j.val)) k =
        subwordRootProduct G expression (fun j => parameters j.val) (min k n) := by
  have h := deodharPrefix_take G expression parameters n k
  rw [deodharPrefix_rootProduct, deodharPrefix_rootProduct, subwordRepresentative_take] at h
  exact mul_right_cancel h

private def extendParameters
    (parameters : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase)
      expression ∪ negativeSteps (weylCoxeterSystem G.rootBase) expression} → K)
    (j : Fin word.length) : K := by
  classical
  exact if hj : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
    negativeSteps (weylCoxeterSystem G.rootBase) expression then parameters ⟨j, hj⟩ else 0

private theorem extend_apply
    (parameters : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase)
      expression ∪ negativeSteps (weylCoxeterSystem G.rootBase) expression} → K)
    (j : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase)
      expression ∪ negativeSteps (weylCoxeterSystem G.rootBase) expression}) :
    extendParameters G expression parameters j.val = parameters j := by
  classical
  simp only [extendParameters, j.property, ↓reduceDIte]

private theorem extend_take
    (parameters : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase)
      expression ∪ negativeSteps (weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) (j : {j : Fin (word.take n).length //
      j ∈ equalSteps (weylCoxeterSystem G.rootBase) (expression.take n) ∪
        negativeSteps (weylCoxeterSystem G.rootBase) (expression.take n)}) :
    extendParameters G expression parameters (Subexpression.takePosition n j.val) =
      parameters (deodharTakeIndex G expression n ⟨j⟩).down := by
  exact extend_apply G expression parameters (deodharTakeIndex G expression n ⟨j⟩).down

/-- Selected root products commute with truncation and the corresponding index map. -/
theorem subwordRootProduct_take
    (parameters : {j : Fin word.length // j ∈ equalSteps (weylCoxeterSystem G.rootBase)
      expression ∪ negativeSteps (weylCoxeterSystem G.rootBase) expression} → K)
    (n k : ℕ) :
    subwordRootProduct G (expression.take n)
      (fun j => parameters (deodharTakeIndex G expression n ⟨j⟩).down) k =
        subwordRootProduct G expression parameters (min k n) := by
  let f := extendParameters G expression parameters
  calc
    _ = subwordRootProduct G (expression.take n)
        (fun j => f (Subexpression.takePosition n j.val)) k :=
      congrArg (fun p => subwordRootProduct G (expression.take n) p k)
        (funext (fun j => (extend_take G expression parameters n j).symm))
    _ = subwordRootProduct G expression (fun j => f j.val) (min k n) :=
      rootProduct_take_raw G expression f n k
    _ = _ := congrArg (fun p => subwordRootProduct G expression p (min k n))
      (funext (extend_apply G expression parameters))

/-- Forgetting later parameters commutes with the regular flag map of a prefix. -/
theorem deodharPrefixMorphism_take (n k : ℕ) :
    deodharParameterProjection G expression n ≫
      deodharPrefixMorphism G (expression.take n) k =
        deodharPrefixMorphism G expression (min k n) := by
  apply mapPoints_injective (X := deodharParameters G expression) (Y := flagVariety G)
  funext x
  let p := fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (mapPoints (deodharParameterInclusion G expression) x) ⟨j⟩
  have hc : (fun j => affineSpaceVarietyPointsEquiv K
      (deodharIndex G (expression.take n))
      (mapPoints (deodharParameterInclusion G (expression.take n))
        (mapPoints (deodharParameterProjection G expression n) x)) ⟨j⟩) =
      (fun j => p (deodharTakeIndex G expression n ⟨j⟩).down) :=
    funext (fun j => deodharParameterProjection_coord G expression n x ⟨j⟩)
  have hroot := (congrArg (fun a => subwordRootProduct G (expression.take n) a k) hc).trans
    (subwordRootProduct_take G expression p n k)
  have hframe := congrArg₂ (fun a b : G.points => a * b) hroot
    (subwordRepresentative_take G expression n k)
  exact (mapPoints_comp (deodharParameterProjection G expression n)
    (deodharPrefixMorphism G (expression.take n) k) x).trans
      ((deodharPrefixMorphism_points G (expression.take n) k _).trans
        ((congrArg (fun g : G.points => flagVarietyPointsEquiv G (flagProjection G g))
          hframe).trans (deodharPrefixMorphism_points G expression (min k n) x).symm))

end
end SchubertGeometry
