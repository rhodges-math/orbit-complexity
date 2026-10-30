import OrbitComplexity.BruhatIntervals.Words.Subexpression
import Mathlib.Data.List.OfFn

/-! # Distinguished subexpressions from prefix paths

A finite prefix path choosing either the identity or the next simple reflection extends
to a distinguished subexpression when every descent forces the reflection. All remaining
letters are retained. The word need not be reduced.

## Main results

* `BruhatIntervals.exists_distinguished_prefix`: extend a path with forced descents.
* `BruhatIntervals.Subexpression.finite`: a finite word has finitely many subexpressions.
-/

namespace BruhatIntervals

noncomputable section

universe u v

variable {S : Type u}

/-- A finite word has only finitely many subexpressions. -/
instance Subexpression.finite (word : List S) : Finite (Subexpression word) := by
  let f : Subexpression word → (Fin word.length → Bool) := fun e j =>
    e.choices[j.val]'(by rw [e.length_choices]; exact j.isLt)
  apply Finite.of_injective f
  intro a b hab
  have hchoices : a.choices = b.choices := by
    apply List.ext_getElem
    · exact a.length_choices.trans b.length_choices.symm
    · intro j hj _
      exact congrFun hab ⟨j, by rw [← a.length_choices]; exact hj⟩
  cases a
  cases b
  cases hchoices
  rfl

variable {W : Type v} [Group W] {M : CoxeterMatrix S}
  (cs : CoxeterSystem M W)

/-- A prefix path with forced descents extends to a distinguished subexpression. -/
theorem exists_distinguished_prefix (word : List S) (n : ℕ) (hn : n ≤ word.length)
    (path : ℕ → W) (hzero : path 0 = 1)
    (hstep : ∀ j (hj : j < n), path (j + 1) = path j ∨
      path (j + 1) = path j * cs.simple (word[j]'(hj.trans_le hn)))
    (hforce : ∀ j (hj : j < n), cs.IsRightDescent (path j) (word[j]'(hj.trans_le hn)) →
      path (j + 1) = path j * cs.simple (word[j]'(hj.trans_le hn))) :
    ∃ expression : Subexpression word, IsDistinguished cs expression ∧
      ∀ k ≤ n, expression.prefixProd cs k = path k := by
  classical
  let expression : Subexpression word :=
    ⟨List.ofFn (fun j : Fin word.length =>
      if j.val < n then decide (path (j.val + 1) = path j.val * cs.simple word[j.val])
      else true), by simp⟩
  have hchoice (j : Fin word.length) :
      expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) =
        if j.val < n then decide (path (j.val + 1) = path j.val * cs.simple word[j.val])
        else true := by
    simp only [expression, List.getElem_ofFn]
  have hprefix : ∀ k, k ≤ n → expression.prefixProd cs k = path k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact (expression.prefixProd_zero cs).trans hzero.symm
    | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      let j : Fin word.length := ⟨k, hkn.trans_le hn⟩
      rw [expression.prefixProd_succ cs j, ih (Nat.le_of_succ_le hk), hchoice j]
      change path k *
        (if (if k < n then decide (path (k + 1) = path k * cs.simple word[k])
          else true) then cs.simple word[k] else 1) = path (k + 1)
      rw [ite_eq_left hkn]
      by_cases hreflect : path (k + 1) = path k * cs.simple word[k]
      · simp [hreflect]
      · have hstay : path (k + 1) = path k := (hstep k hkn).resolve_right hreflect
        simp [hstay]
  refine ⟨expression, (isDistinguished_iff_forced cs expression).mpr ?_, hprefix⟩
  intro j hdesc
  rw [hchoice j]
  by_cases hj : j.val < n
  · have hdescent : cs.IsRightDescent (path j.val) word[j.val] := by
      rwa [hprefix j.val (Nat.le_of_lt hj)] at hdesc
    simp [hj, hforce j.val hj hdescent]
  · simp [hj]

end

end BruhatIntervals
