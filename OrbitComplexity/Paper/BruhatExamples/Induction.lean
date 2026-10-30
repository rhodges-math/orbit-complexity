import OrbitComplexity.Paper.BruhatExamples.Permutations
import OrbitComplexity.BruhatIntervals.Permutations.Intervals
import OrbitComplexity.BruhatIntervals.Graph.Recursion

/-!
# The interval recursion example

The intervals `[1324,3412]` and `[1234,3142]` have the same label span, although their
rank sizes differ. Their top-cover roots give two explicit generating sets for that span.
-/

namespace SchubertOrbits.BruhatExamples

open BruhatIntervals

private theorem lower_length : (TypeA.coxeterSystem 3).length lower1324 = 1 := by
  rw [TypeA.length_eq_inversions]
  unfold TypeA.inversionPairs
  rw [show (⇑lower1324 : Fin 4 → Fin 4) =
    (fun i => if i = 1 then 2 else if i = 2 then 1 else i) from funext lower1324_apply]
  decide

private theorem upper_length : (TypeA.coxeterSystem 3).length upper3412 = 4 := by
  rw [TypeA.length_eq_inversions]
  unfold TypeA.inversionPairs
  rw [show (⇑upper3412 : Fin 4 → Fin 4) =
    (fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1) from
      funext upper3412_apply]
  decide

private theorem shortened_length : (TypeA.coxeterSystem 3).length upper3142 = 3 := by
  rw [TypeA.length_eq_inversions]
  unfold TypeA.inversionPairs
  rw [show (⇑upper3142 : Fin 4 → Fin 4) =
    (fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else 1) from
      funext upper3142_apply]
  decide

private theorem first_ranks (k : ℕ) :
    rankSize (TypeA.coxeterSystem 3) lower1324 upper3412 k =
      if k = 0 ∨ k = 3 then 1 else if k = 1 ∨ k = 2 then 4 else 0 := by
  by_cases hk : k < 4
  · rw [TypeA.rankSize_eq_filter_card]
    have hsmall : ∀ j : Fin 4,
        ((TypeA.intervalElements 3 lower1324 upper3412).filter (fun w =>
          (TypeA.inversionPairs 3 w).card =
            (TypeA.inversionPairs 3 lower1324).card + j.val)).card =
          if j.val = 0 ∨ j.val = 3 then 1 else if j.val = 1 ∨ j.val = 2 then 4 else 0 :=
      by decide
    exact hsmall ⟨k, hk⟩
  · have hfirst : ¬ (k = 0 ∨ k = 3) := by omega
    have hmiddle : ¬ (k = 1 ∨ k = 2) := by omega
    rw [ite_eq_right hfirst, ite_eq_right hmiddle]
    apply rankSize_eq_zero_of_lt
    rw [lower_length, upper_length]
    omega

private theorem second_ranks (k : ℕ) :
    rankSize (TypeA.coxeterSystem 3) 1 upper3142 k =
      if k = 0 ∨ k = 3 then 1 else if k = 1 ∨ k = 2 then 3 else 0 := by
  by_cases hk : k < 4
  · rw [TypeA.rankSize_eq_filter_card]
    have hsmall : ∀ j : Fin 4,
        ((TypeA.intervalElements 3 1 upper3142).filter (fun w =>
          (TypeA.inversionPairs 3 w).card =
            (TypeA.inversionPairs 3 1).card + j.val)).card =
          if j.val = 0 ∨ j.val = 3 then 1 else if j.val = 1 ∨ j.val = 2 then 3 else 0 :=
      by decide
    exact hsmall ⟨k, hk⟩
  · have hfirst : ¬ (k = 0 ∨ k = 3) := by omega
    have hmiddle : ¬ (k = 1 ∨ k = 2) := by omega
    rw [ite_eq_right hfirst, ite_eq_right hmiddle]
    apply rankSize_eq_zero_of_lt
    rw [(TypeA.coxeterSystem 3).length_one, shortened_length]
    omega

private theorem displayed_spans : Submodule.span ℝ
    ({TypeA.root 3 0 2, TypeA.root 3 1 2, TypeA.root 3 0 3,
      TypeA.root 3 1 3} : Set (Fin 4 → ℝ)) =
    Submodule.span ℝ ({TypeA.root 3 0 2, TypeA.root 3 1 2,
      TypeA.root 3 1 3} : Set (Fin 4 → ℝ)) := by
  have hroot : TypeA.root 3 0 3 =
      TypeA.root 3 0 2 - TypeA.root 3 1 2 + TypeA.root 3 1 3 := by
    ext k
    simp only [TypeA.root, Pi.sub_apply, Pi.add_apply]
    ring
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro α hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hroot]
      exact Submodule.add_mem _ (Submodule.sub_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_mono
    intro α hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
    tauto

/-- The two intervals related by the descent at position two have equal label spaces,
different rank sequences, and the displayed top-cover generating sets with equal spans. -/
theorem ad_induction_example :
    let cs := TypeA.coxeterSystem 3
    let realization := TypeA.realization 3
    let u := lower1324
    let v := upper3412
    let v' := upper3142
    u * cs.simple 1 = 1 ∧ v * cs.simple 1 = v' ∧
      labelSpan realization u v = labelSpan realization 1 v' ∧
      algebraicDim realization u v = algebraicDim realization 1 v' ∧
      (∀ k : ℕ, rankSize cs u v k =
        if k = 0 ∨ k = 3 then 1 else if k = 1 ∨ k = 2 then 4 else 0) ∧
      (∀ k : ℕ, rankSize cs 1 v' k =
        if k = 0 ∨ k = 3 then 1 else if k = 1 ∨ k = 2 then 3 else 0) ∧
      {α | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj x v,
        cs.length v = cs.length x + 1 ∧ edgeLabel realization x v h = α} =
          {TypeA.root 3 0 2, TypeA.root 3 1 2, TypeA.root 3 0 3, TypeA.root 3 1 3} ∧
      {α | ∃ x ∈ bruhatInterval cs 1 v', ∃ h : (bruhatGraph cs).Adj x v',
        cs.length v' = cs.length x + 1 ∧ edgeLabel realization x v' h = α} =
          {TypeA.root 3 0 2, TypeA.root 3 1 2, TypeA.root 3 1 3} ∧
      Submodule.span ℝ
        ({TypeA.root 3 0 2, TypeA.root 3 1 2, TypeA.root 3 0 3,
          TypeA.root 3 1 3} : Set (Fin 4 → ℝ)) =
        Submodule.span ℝ ({TypeA.root 3 0 2, TypeA.root 3 1 2,
          TypeA.root 3 1 3} : Set (Fin 4 → ℝ)) := by
  dsimp only
  have hfirst : lower1324 * (TypeA.coxeterSystem 3).simple 1 = 1 := by
    rw [TypeA.coxeterSystem_simple]
    decide
  have hsecond : upper3412 * (TypeA.coxeterSystem 3).simple 1 = upper3142 := by
    rw [TypeA.coxeterSystem_simple]
    rfl
  have horder : (TypeA.coxeterSystem 3).BruhatLE lower1324 upper3412 := by
    rw [← TypeA.mem_subwordProducts]
    decide
  have hlower : (TypeA.coxeterSystem 3).IsRightDescent lower1324 1 :=
    (TypeA.isRightDescent_iff 3 lower1324 1).mpr (by decide)
  have hupper : (TypeA.coxeterSystem 3).IsRightDescent upper3412 1 :=
    (TypeA.isRightDescent_iff 3 upper3412 1).mpr (by decide)
  have hspan := (labelSpan_recursion (TypeA.realization 3) lower1324 upper3412
    horder 1 hupper).1 hlower
  rw [hfirst, hsecond] at hspan
  refine ⟨hfirst, hsecond, hspan,
    congrArg (fun plane : Submodule ℝ (Fin 4 → ℝ) => Module.finrank ℝ plane) hspan,
    first_ranks, second_ranks, ?_, ?_, displayed_spans⟩
  · rw [TypeA.topCoverLabels_eq]
    have hpairs : TypeA.topCoverPairs 3 lower1324 upper3412 =
        {(0, 2), (1, 2), (0, 3), (1, 3)} := by decide
    rw [hpairs]
    simp
  · rw [TypeA.topCoverLabels_eq]
    have hpairs : TypeA.topCoverPairs 3 1 upper3142 = {(0, 2), (1, 2), (1, 3)} := by decide
    rw [hpairs]
    simp

end SchubertOrbits.BruhatExamples
