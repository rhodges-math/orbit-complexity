import OrbitComplexity.Paper.Deodhar.Roots
import OrbitComplexity.BruhatIntervals.Graph.Recursion
import OrbitComplexity.BruhatIntervals.Words.Subword

/-! # Subexpression spans and interval spans

The last position of a distinguished subexpression gives three cases. Increasing positions
preserve its root span, omitted positions add the recurrence's edge line, and decreasing
positions contribute an edge already contained in the larger interval. Positive distinguished
subexpressions have only the first two cases, so their span is the whole interval label span.

## Main results

* `subwordWeightSpan_interval`: inclusion for distinguished subexpressions and equality for
  positive distinguished subexpressions.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson Varieties*,
  Theorem 1.4.
-/

namespace SchubertOrbits

open BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem final_nonconstant {word : List Index} (expression : Subexpression word)
    (j : Fin word.length)
    (hne : expression.prefixProd cs (j.val + 1) ≠ expression.prefixProd cs j.val) :
    expression.prefixProd cs (j.val + 1) =
      expression.prefixProd cs j.val * cs.simple word[j.val] := by
  have h := expression.prefixProd_succ cs j
  split at h
  · exact h
  · exact (hne (by simpa only [mul_one] using h)).elim

private theorem wordProd_last {word : List Index} (j : Fin word.length)
    (hlast : j.val + 1 = word.length) :
    cs.wordProd word = cs.wordProd (word.take j.val) * cs.simple word[j.val] := by
  change (word.map cs.simple).prod = ((word.take j.val).map cs.simple).prod * _
  have h : (word.map cs.simple).take (j.val + 1) = word.map cs.simple := by
    rw [hlast, ← List.length_map (f := cs.simple), List.take_length]
  rw [← h, List.prod_take_succ _ _ (by simpa only [List.length_map] using j.isLt)]
  simp only [List.getElem_map, List.map_take]

private theorem interval_span_aux (n : ℕ) :
    ∀ {word : List Index} (expression : Subexpression word), word.length = n →
      cs.IsReduced word → IsDistinguished cs expression →
      subwordWeightSpan realization expression ≤
        labelSpan realization (expression.prefixProd cs word.length) (cs.wordProd word) ∧
      (IsPositive cs expression → subwordWeightSpan realization expression =
        labelSpan realization (expression.prefixProd cs word.length) (cs.wordProd word)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro word expression hlen hred hd
    by_cases hz : word.length = 0
    · have hw : word = [] := List.eq_nil_of_length_eq_zero hz
      subst word
      have hspan : subwordWeightSpan realization expression = ⊥ := by
        apply le_antisymm ?_ bot_le
        apply Submodule.span_le.mpr
        rintro α ⟨j, _, _⟩
        exact Fin.elim0 j
      simp only [List.length_nil, Subexpression.prefixProd_zero, cs.wordProd_nil,
        labelSpan_self, hspan, le_refl, implies_true, and_self]
    · let j : Fin word.length := ⟨word.length - 1, by omega⟩
      have hlast : j.val + 1 = word.length := by dsimp [j]; omega
      have hsmall : (word.take j.val).length < n := by
        simp only [List.length_take, Nat.min_eq_left j.isLt.le]
        omega
      have hprior := ih (word.take j.val).length hsmall (expression.take j.val) rfl
        (hred.take j.val) (hd.take cs j.val)
      simp only [List.length_take, Nat.min_eq_left j.isLt.le,
        Subexpression.prefixProd_take, Nat.min_self] at hprior
      have hbelow : cs.BruhatLE (expression.prefixProd cs word.length) (cs.wordProd word) :=
        (subexpression_subword_property cs hred rfl).mpr ⟨expression, rfl⟩
      have hprefixbelow : cs.BruhatLE (expression.prefixProd cs j.val)
          (cs.wordProd (word.take j.val)) := by
        have h := (subexpression_subword_property cs (hred.take j.val) rfl).mpr
          ⟨expression.take j.val, rfl⟩
        simpa only [List.length_take, Nat.min_eq_left j.isLt.le,
          Subexpression.prefixProd_take, Nat.min_self] using h
      have hvprod := wordProd_last (cs := cs) j hlast
      have hpreviousLength : cs.length (cs.wordProd (word.take j.val)) = j.val := by
        simpa only [List.length_take, Nat.min_eq_left j.isLt.le] using (hred.take j.val).eq
      have hv : cs.IsRightDescent (cs.wordProd word) word[j.val] := by
        change cs.length (cs.wordProd word * cs.simple word[j.val]) < cs.length (cs.wordProd word)
        rw [hvprod, cs.simple_mul_simple_cancel_right, hpreviousLength, ← hvprod, hred.eq]
        exact j.isLt
      have hvprev : cs.wordProd word * cs.simple word[j.val] =
          cs.wordProd (word.take j.val) := by
        rw [hvprod, cs.simple_mul_simple_cancel_right]
      have htop : cs.BruhatLE (cs.wordProd (word.take j.val)) (cs.wordProd word) := by
        rw [← hvprev]
        exact (cs.bruhatStep_mul_simple_of_isRightDescent _ hv).bruhatLE
      rcases mem_step_sets cs expression j with hpositive | hequal | hnegative
      · have hmul := final_nonconstant expression j hpositive.2.symm
        have hfinal : expression.prefixProd cs word.length =
            expression.prefixProd cs j.val * cs.simple word[j.val] := by
          simpa only [hlast] using hmul
        have hcancel : expression.prefixProd cs word.length * cs.simple word[j.val] =
            expression.prefixProd cs j.val := by
          rw [hfinal, cs.simple_mul_simple_cancel_right]
        have hu : cs.IsRightDescent (expression.prefixProd cs word.length) word[j.val] := by
          change cs.length (expression.prefixProd cs word.length * cs.simple word[j.val]) <
            cs.length (expression.prefixProd cs word.length)
          rw [hcancel]
          simpa only [hlast] using hpositive.1.length_lt_of_ne hpositive.2
        have hrec := (labelSpan_recursion realization _ _ hbelow word[j.val] hv).1 hu
        rw [hcancel, hvprev] at hrec
        have hspan := subwordWeightSpan_last_positive realization expression j hlast hpositive
        constructor
        · rw [hspan, hrec]
          exact hprior.1
        · intro hp
          exact hspan.trans ((hprior.2 (hp.take cs j.val)).trans hrec.symm)
      · have hu : ¬ cs.IsRightDescent (expression.prefixProd cs word.length) word[j.val] := by
          intro hu
          have hle := hd j
          have heq : expression.prefixProd cs (j.val + 1) = expression.prefixProd cs word.length :=
            congrArg (expression.prefixProd cs) hlast
          have hp : expression.prefixProd cs j.val = expression.prefixProd cs word.length :=
            hequal.trans heq
          rw [heq, hp] at hle
          exact (Nat.not_lt_of_ge hle.length_le) hu
        have hp : expression.prefixProd cs j.val = expression.prefixProd cs word.length := by
          exact hequal.trans (congrArg (expression.prefixProd cs) hlast)
        have hrec := (labelSpan_recursion realization _ _ hbelow word[j.val] hv).2 hu
        rw [hvprev] at hrec
        have hroot := subwordRoot_eq_edgeLabel realization expression hd j (Or.inl hequal)
        rw [hp] at hroot
        have hspan := subwordWeightSpan_last realization expression j hlast (Or.inl hequal)
        rw [hp] at hprior
        constructor
        · rw [hspan, hrec, hroot]
          exact sup_le_sup_right hprior.1 _
        · intro hpositive
          rw [hspan, hrec, hroot, hprior.2 (hpositive.take cs j.val)]
      · have hspan := subwordWeightSpan_last realization expression j hlast (Or.inr hnegative)
        have hdown : cs.BruhatLE (expression.prefixProd cs word.length)
            (expression.prefixProd cs j.val) := by
          simpa only [hlast] using hnegative.1
        have hroot : subwordRoot realization expression j ∈
            labelSpan realization (expression.prefixProd cs word.length) (cs.wordProd word) := by
          obtain ⟨hedge, hlabel⟩ := subwordRoot_negative_edge realization expression hd j hnegative
          simp only [hlast] at hedge hlabel
          exact Submodule.subset_span
            ⟨_, ⟨cs.bruhatLE_refl _, hbelow⟩,
              _, ⟨hdown, hprefixbelow.trans htop⟩, hedge, hlabel.symm⟩
        constructor
        · rw [hspan]
          apply sup_le (hprior.1.trans (labelSpan_mono realization hdown htop))
          apply Submodule.span_le.mpr
          intro α hα
          have hαeq : α = subwordRoot realization expression j := Set.mem_singleton_iff.mp hα
          rw [hαeq]
          exact hroot
        · intro hp
          exact (hnegative.2 (hnegative.1.antisymm (hp j))).elim

/-- Distinguished subexpression weights lie in the interval label span;
positivity gives equality. -/
theorem subwordWeightSpan_interval {word : List Index} (expression : Subexpression word)
    (hred : cs.IsReduced word) (hd : IsDistinguished cs expression) :
    subwordWeightSpan realization expression ≤
      labelSpan realization (expression.prefixProd cs word.length) (cs.wordProd word) ∧
    (IsPositive cs expression → subwordWeightSpan realization expression =
      labelSpan realization (expression.prefixProd cs word.length) (cs.wordProd word)) :=
  interval_span_aux realization word.length expression rfl hred hd

end SchubertOrbits
