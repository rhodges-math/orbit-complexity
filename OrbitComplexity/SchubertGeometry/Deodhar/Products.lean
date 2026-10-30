import OrbitComplexity.SchubertGeometry.Deodhar.RootMaps
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Group

/-! # Ordered root products of subexpressions

The ordered conjugated root parameters factor each signed prefix product.
-/

noncomputable section
namespace SchubertGeometry
open BruhatIntervals ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def selectedPosition (j : Fin word.length) : Option
    {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} := by
  classical
  exact if h : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    some ⟨j, h⟩ else none

/-- The ordered product of selected conjugated root maps among the first `n` word positions. -/
def subwordRootProduct (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) : G.points :=
  (((List.finRange word.length).take n).filterMap (selectedPosition G expression)).map
    (fun j => gaParameterPoint (subwordRootMap G expression j) (parameters j)) |>.prod

private def positionFactor (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (j : Fin word.length) :
    G.points := by
  classical
  exact if h : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    gaParameterPoint (subwordRootMap G expression ⟨j, h⟩) (parameters ⟨j, h⟩) else 1

private theorem selected_prod (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (positions : List (Fin word.length)) :
    ((positions.filterMap (selectedPosition G expression)).map
      (fun j => gaParameterPoint (subwordRootMap G expression j) (parameters j))).prod =
      (positions.map (positionFactor G expression parameters)).prod := by
  classical
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    by_cases hj : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
    · simp only [List.filterMap_cons, selectedPosition, positionFactor, hj, ↓reduceDIte,
        List.map_cons, List.prod_cons, ih]
    · simp only [List.filterMap_cons, selectedPosition, positionFactor, hj, ↓reduceDIte,
        List.map_cons, List.prod_cons, one_mul, ih]

private theorem product_ofFn (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K) (n : ℕ) :
    subwordRootProduct G expression parameters n =
      ((List.ofFn (positionFactor G expression parameters)).take n).prod := by
  rw [subwordRootProduct, selected_prod, List.map_take, ← List.ofFn_eq_map]

private theorem factor_conjugated (parameters : Fin word.length → K) (j : Fin word.length) :
    positionFactor G expression (fun j => parameters j.val) j =
      subwordRepresentative G expression j.val * deodharRootElement G expression parameters j *
        (subwordRepresentative G expression j.val)⁻¹ := by
  classical
  by_cases hn : j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
  · have hj : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := Or.inr hn
    simp only [positionFactor, hj, ↓reduceDIte]
    exact subwordRootMap_point G expression parameters ⟨j, hj⟩
  · by_cases he : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
    · have hj : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := Or.inl he
      simp only [positionFactor, hj, ↓reduceDIte]
      exact subwordRootMap_point G expression parameters ⟨j, hj⟩
    · have hj : j ∉ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
          negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression :=
        fun h => h.elim he hn
      simp only [positionFactor, hj, ↓reduceDIte, deodharRootElement, hn, he, ↓reduceIte,
        mul_one, mul_inv_cancel]

private theorem product_succ (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (j : Fin word.length) :
    subwordRootProduct G expression parameters (j.val + 1) =
      subwordRootProduct G expression parameters j.val *
        positionFactor G expression parameters j := by
  rw [product_ofFn, List.prod_take_succ _ _ (by simpa only [List.length_ofFn] using j.isLt),
    List.getElem_ofFn, ← product_ofFn]

private theorem prefix_succ (parameters : Fin word.length → K) (j : Fin word.length) :
    deodharPrefix G expression parameters (j.val + 1) =
      deodharPrefix G expression parameters j.val * deodharStep G expression parameters j := by
  simp only [deodharPrefix]
  rw [List.prod_take_succ _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]

private theorem representative_succ (j : Fin word.length) :
    subwordRepresentative G expression (j.val + 1) =
      subwordRepresentative G expression j.val * subwordStepPoint G expression j := by
  simp only [subwordRepresentative]
  rw [List.prod_take_succ _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]

set_option maxHeartbeats 400000 in
private theorem prefix_step (parameters : Fin word.length → K) (j : Fin word.length)
    (ih : deodharPrefix G expression parameters j.val =
      subwordRootProduct G expression (fun j => parameters j.val) j.val *
        subwordRepresentative G expression j.val) :
    deodharPrefix G expression parameters (j.val + 1) =
      subwordRootProduct G expression (fun j => parameters j.val) (j.val + 1) *
        subwordRepresentative G expression (j.val + 1) := by
  rw [prefix_succ, product_succ, representative_succ, factor_conjugated, ih, deodharStep]
  group

private theorem take_stable {A : Type*} (l : List A) (n : ℕ) (hn : l.length ≤ n) :
    l.take (n + 1) = l.take n := by
  rw [List.take_of_length_le (Nat.le_succ_of_le hn), List.take_of_length_le hn]

private theorem prefix_stable (parameters : Fin word.length → K) (n : ℕ)
    (hn : word.length ≤ n) :
    deodharPrefix G expression parameters (n + 1) = deodharPrefix G expression parameters n := by
  unfold deodharPrefix
  rw [take_stable _ n (by simpa only [List.length_ofFn] using hn)]

private theorem representative_stable (n : ℕ) (hn : word.length ≤ n) :
    subwordRepresentative G expression (n + 1) = subwordRepresentative G expression n := by
  unfold subwordRepresentative
  rw [take_stable _ n (by simpa only [List.length_ofFn] using hn)]

private theorem product_stable (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) (hn : word.length ≤ n) :
    subwordRootProduct G expression parameters (n + 1) =
      subwordRootProduct G expression parameters n := by
  unfold subwordRootProduct
  rw [take_stable _ n (by simpa only [List.length_finRange] using hn)]

/-- Each Deodhar prefix is the ordered selected-root product times its signed representative. -/
theorem deodharPrefix_rootProduct (parameters : Fin word.length → K) (n : ℕ) :
    deodharPrefix G expression parameters n =
      subwordRootProduct G expression (fun j => parameters j.val) n *
        subwordRepresentative G expression n := by
  induction n with
  | zero =>
    simp only [deodharPrefix, subwordRootProduct, subwordRepresentative, List.take_zero,
      List.filterMap_nil, List.map_nil, List.prod_nil, mul_one]
  | succ n ih =>
    by_cases hn : n < word.length
    · exact prefix_step G expression parameters ⟨n, hn⟩ ih
    · have hnlen : word.length ≤ n := Nat.le_of_not_gt hn
      rw [prefix_stable G expression parameters n hnlen,
        product_stable G expression (fun j => parameters j.val) n hnlen,
        representative_stable G expression n hnlen]
      exact ih

end SchubertGeometry
