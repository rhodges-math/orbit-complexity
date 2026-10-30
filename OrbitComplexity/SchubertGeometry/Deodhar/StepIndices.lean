import OrbitComplexity.SchubertGeometry.Deodhar.ParameterPrefixes
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterProduct

/-!
# Parameter indices at one subexpression step

An increasing step retains the prefix parameter indices. An omitted or decreasing step
adds one final index, which is an omitted coordinate exactly when the step is equal.
The identifications preserve the underlying word positions and the omitted-coordinate sets.
-/

open BruhatIntervals

noncomputable section
namespace SchubertGeometry
universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def prefixIndex (m : ℕ) (j : deodharIndex G expression)
    (hm : j.down.val.val < m) : deodharIndex G (expression.take m) := by
  let p : Fin (word.take m).length := ⟨j.down.val.val, by
    simp only [List.length_take]
    exact Nat.lt_min.mpr ⟨hm, j.down.val.isLt⟩⟩
  refine ⟨⟨p, ?_⟩⟩
  have hp : Subexpression.takePosition m p = j.down.val := Fin.ext rfl
  rcases j.down.property with he | hn
  · exact Or.inl ((expression.equalSteps_take
      (ReductiveGroups.weylCoxeterSystem G.rootBase) m p).mpr (hp.symm ▸ he))
  · exact Or.inr ((expression.negativeSteps_take
      (ReductiveGroups.weylCoxeterSystem G.rootBase) m p).mpr (hp.symm ▸ hn))

private theorem index_lt (m : ℕ) (j : deodharIndex G (expression.take m)) :
    j.down.val.val < m := by
  have hj := j.down.val.isLt
  simp only [List.length_take] at hj
  omega

private theorem positive_not_selected (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    n ∉ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := by
  rintro (he | hd)
  · exact hn.2 he
  · exact hn.2 (hn.1.antisymm hd.1)

private theorem positive_index_lt (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (j : deodharIndex G (expression.take (n.val + 1))) : j.down.val.val < n.val := by
  have hj := index_lt G expression (n.val + 1) j
  have hs := (deodharTakeIndex G expression (n.val + 1) j).down.property
  have hne : j.down.val.val ≠ n.val := by
    intro he
    have hp : (deodharTakeIndex G expression (n.val + 1) j).down.val = n := Fin.ext he
    rw [hp] at hs
    exact positive_not_selected G expression n hn hs
  omega

private theorem index_ext {m : ℕ}
    (j k : deodharIndex G (expression.take m)) (h : j.down.val.val = k.down.val.val) :
    j = k := by
  apply ULift.ext
  exact Subtype.ext (Fin.ext h)

private def stepLeft (n : Fin word.length) (j : deodharIndex G (expression.take n.val)) :
    deodharIndex G (expression.take (n.val + 1)) :=
  prefixIndex G expression (n.val + 1) (deodharTakeIndex G expression n.val j) (by
    have := index_lt G expression n.val j
    change j.down.val.val < n.val + 1
    omega)

private theorem stepLeft_val (n : Fin word.length)
    (j : deodharIndex G (expression.take n.val)) :
    (stepLeft G expression n j).down.val.val = j.down.val.val := rfl

private def stepLower (n : Fin word.length)
    (j : deodharIndex G (expression.take (n.val + 1))) (hj : j.down.val.val < n.val) :
    deodharIndex G (expression.take n.val) :=
  prefixIndex G expression n.val (deodharTakeIndex G expression (n.val + 1) j) hj

private theorem stepLower_val (n : Fin word.length)
    (j : deodharIndex G (expression.take (n.val + 1))) (hj : j.down.val.val < n.val) :
    (stepLower G expression n j hj).down.val.val = j.down.val.val := rfl

private def stepRight (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharIndex G (expression.take (n.val + 1)) :=
  prefixIndex G expression (n.val + 1) ⟨⟨n, hn⟩⟩ (Nat.lt_succ_self _)

private theorem stepRight_val (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (stepRight G expression n hn).down.val.val = n.val := rfl

private def stepForward (n : Fin word.length)
    (j : deodharIndex G (expression.take (n.val + 1))) :
    deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1} :=
  if hj : j.down.val.val < n.val then Sum.inl (stepLower G expression n j hj)
  else Sum.inr PUnit.unit

private def stepBackward (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1} →
      deodharIndex G (expression.take (n.val + 1)) :=
  Sum.elim (stepLeft G expression n) (fun _ => stepRight G expression n hn)

private theorem backward_forward (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (j : deodharIndex G (expression.take (n.val + 1))) :
    stepBackward G expression n hn (stepForward G expression n j) = j := by
  unfold stepForward
  split_ifs with hj
  · change stepLeft G expression n (stepLower G expression n j hj) = j
    apply index_ext
    rw [stepLeft_val, stepLower_val]
  · change stepRight G expression n hn = j
    apply index_ext
    rw [stepRight_val]
    have := index_lt G expression (n.val + 1) j
    omega

private theorem forward_backward (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (j : deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1}) :
    stepForward G expression n (stepBackward G expression n hn j) = j := by
  cases j with
  | inl j =>
    change stepForward G expression n (stepLeft G expression n j) = Sum.inl j
    have hj : (stepLeft G expression n j).down.val.val < n.val := by
      rw [stepLeft_val]
      exact index_lt G expression n.val j
    rw [stepForward, dite_eq_left hj]
    apply congrArg Sum.inl
    apply index_ext
    rw [stepLower_val, stepLeft_val]
  | inr j =>
    cases j
    change stepForward G expression n (stepRight G expression n hn) = Sum.inr PUnit.unit
    have hj : ¬ (stepRight G expression n hn).down.val.val < n.val := by
      rw [stepRight_val]
      exact Nat.lt_irrefl _
    rw [stepForward, dite_eq_right hj]

/-- At an increasing step, the new prefix has exactly the old parameter indices. -/
def deodharStepIndexPositive (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharIndex G (expression.take (n.val + 1)) ≃ deodharIndex G (expression.take n.val) where
  toFun j := prefixIndex G expression n.val
    (deodharTakeIndex G expression (n.val + 1) j) (positive_index_lt G expression n hn j)
  invFun j := prefixIndex G expression (n.val + 1)
    (deodharTakeIndex G expression n.val j) (by
      have := index_lt G expression n.val j
      change j.down.val.val < n.val + 1
      omega)
  left_inv j := by
    apply ULift.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv j := by
    apply ULift.ext
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- At an omitted or decreasing step, the final position gives one new parameter index. -/
def deodharStepIndexSelected (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharIndex G (expression.take (n.val + 1)) ≃
      deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1} where
  toFun := stepForward G expression n
  invFun := stepBackward G expression n hn
  left_inv := backward_forward G expression n hn
  right_inv := forward_backward G expression n hn

/-- The increasing-step identification preserves the underlying word position. -/
theorem deodharStepIndexPositive_val (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (j : deodharIndex G (expression.take n.val)) :
    ((deodharStepIndexPositive G expression n hn).symm j).down.val.val = j.down.val.val := rfl

/-- The selected-step inverse retains old positions and assigns the last position to the unit. -/
theorem deodharStepIndexSelected_val (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (∀ j : deodharIndex G (expression.take n.val),
      ((deodharStepIndexSelected G expression n hn).symm (Sum.inl j)).down.val.val =
        j.down.val.val) ∧
    ((deodharStepIndexSelected G expression n hn).symm (Sum.inr PUnit.unit)).down.val.val =
      n.val := ⟨fun _ => rfl, rfl⟩

private theorem equalPosition_iff (m : ℕ) (j : deodharIndex G (expression.take m)) :
    j ∈ deodharEqualPositions G (expression.take m) ↔
      (deodharTakeIndex G expression m j).down.val ∈
        equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := by
  classical
  simp only [deodharEqualPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact expression.equalSteps_take (ReductiveGroups.weylCoxeterSystem G.rootBase) m j.down.val

private theorem equalPosition_value (m : ℕ) (j : deodharIndex G (expression.take m))
    (k : Fin word.length) (hk : j.down.val.val = k.val) :
    j ∈ deodharEqualPositions G (expression.take m) ↔
      k ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := by
  have hp : (deodharTakeIndex G expression m j).down.val = k := Fin.ext hk
  exact (equalPosition_iff G expression m j).trans (Iff.of_eq
    (congrArg (fun p => p ∈ equalSteps
      (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) hp))

private theorem equalPosition_congr (m l : ℕ)
    (j : deodharIndex G (expression.take m)) (k : deodharIndex G (expression.take l))
    (hk : j.down.val.val = k.down.val.val) :
    j ∈ deodharEqualPositions G (expression.take m) ↔
      k ∈ deodharEqualPositions G (expression.take l) :=
  (equalPosition_value G expression m j (deodharTakeIndex G expression l k).down.val hk).trans
    (equalPosition_iff G expression l k).symm

/-- The increasing-step identification preserves the omitted coordinate positions. -/
theorem deodharEqualPositions_positive (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (deodharEqualPositions G (expression.take (n.val + 1))).map
        (deodharStepIndexPositive G expression n hn).toEmbedding =
      deodharEqualPositions G (expression.take n.val) := by
  classical
  ext j
  rw [Finset.mem_map_equiv, equalPosition_iff, equalPosition_iff]
  have hp : (deodharTakeIndex G expression (n.val + 1)
      ((deodharStepIndexPositive G expression n hn).symm j)).down.val =
      (deodharTakeIndex G expression n.val j).down.val := by
    apply Fin.ext
    exact deodharStepIndexPositive_val G expression n hn j
  rw [hp]

/-- A selected final position is omitted exactly when it is an equal step. -/
theorem deodharEqualPositions_selected (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (deodharEqualPositions G (expression.take (n.val + 1))).map
        (deodharStepIndexSelected G expression n hn).toEmbedding =
      if n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
        insert (Sum.inr PUnit.unit)
          ((deodharEqualPositions G (expression.take n.val)).map Function.Embedding.inl)
      else (deodharEqualPositions G (expression.take n.val)).map Function.Embedding.inl := by
  classical
  ext j
  refine (Finset.mem_map_equiv
    (s := deodharEqualPositions G (expression.take (n.val + 1)))
    (f := deodharStepIndexSelected G expression n hn) (b := j)).trans ?_
  cases j with
  | inl j =>
    have he := equalPosition_congr G expression (n.val + 1) n.val
      ((deodharStepIndexSelected G expression n hn).symm (Sum.inl j)) j
      ((deodharStepIndexSelected_val G expression n hn).1 j)
    exact he.trans (by split_ifs <;> simp)
  | inr j =>
    cases j
    have he := equalPosition_value G expression (n.val + 1)
      ((deodharStepIndexSelected G expression n hn).symm (Sum.inr PUnit.unit)) n
      (deodharStepIndexSelected_val G expression n hn).2
    exact he.trans (by split_ifs with hc <;> simp [hc, Finset.mem_map])

end SchubertGeometry
