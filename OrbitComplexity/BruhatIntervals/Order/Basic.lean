import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# Subwords and the lifting property

This file gives the subword characterization and both conclusions of the lifting property for
every Coxeter system. It also gives the descent recurrence for Bruhat comparisons.

## Main results

* `subword_property`: Bruhat comparison is represented by subwords of any fixed reduced word.
* `lifting_property`: a right descent of the upper endpoint lifts a right ascent of the lower one.
* `bruhatLE_descent_iff`: multiplying both endpoints by a common right descent preserves comparison.

## Implementation notes

The order is `CoxeterSystem.BruhatLE`; no global order instance is assigned to the group.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- For a fixed reduced word of `w`, an element is below `w` exactly when a subword evaluates to it.
This is the subword property of Björner–Brenti, Section 2.2. -/
theorem subword_property {u w : W} {word : List S} (hred : cs.IsReduced word)
    (hword : cs.wordProd word = w) :
    cs.BruhatLE u w ↔ ∃ subword : List S, subword.Sublist word ∧ cs.wordProd subword = u := by
  subst w
  exact cs.bruhatLE_iff_exists_sublist_wordProd_eq hred

/-- If `i` lengthens the lower endpoint, that endpoint remains below the right-multiplied upper
endpoint. -/
theorem bruhatLE_mul_of_ascent {u w : W} (h : cs.BruhatLE u w) (i : S)
    (hu : ¬ cs.IsRightDescent u i) :
    cs.BruhatLE u (w * cs.simple i) := by
  obtain ⟨word, hred, hword⟩ := cs.exists_isReduced (w * cs.simple i)
  have hprod : cs.wordProd (word ++ [i]) = w := by
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hword,
      cs.simple_mul_simple_cancel_right]
  obtain ⟨subword, hsub, hsubprod, hsublen⟩ :=
    h.exists_sublist_wordProd_eq_length_eq (word ++ [i]) hprod
  obtain ⟨initial, last, rfl, hinitial, hlast⟩ := List.sublist_append_iff.mp hsub
  rcases List.sublist_singleton.mp hlast with rfl | rfl
  · rw [List.append_nil] at hsubprod
    rw [hword, ← hsubprod]
    exact cs.bruhatLE_wordProd_of_sublist hred hinitial
  · have hinitialprod : cs.wordProd initial = u * cs.simple i := by
      rw [← hsubprod, cs.wordProd_append, cs.wordProd_singleton,
        cs.simple_mul_simple_cancel_right]
    have hlen := cs.length_wordProd_le initial
    rw [hinitialprod, cs.not_isRightDescent_iff.mp hu] at hlen
    simp only [List.length_append, List.length_singleton] at hsublen
    omega

/-- If `u < w` and `i` is a right descent of `w` and a right ascent of `u`, then `u ≤ w sᵢ` and
`u sᵢ ≤ w`. This is the lifting property of Björner–Brenti, Section 2.2. -/
theorem lifting_property {u w : W} (h : cs.BruhatLE u w ∧ u ≠ w) (i : S)
    (hw : cs.IsRightDescent w i) (hu : ¬ cs.IsRightDescent u i) :
    cs.BruhatLE u (w * cs.simple i) ∧ cs.BruhatLE (u * cs.simple i) w :=
  ⟨bruhatLE_mul_of_ascent cs h.1 i hu, h.1.mul_simple_of_isRightDescent i hw⟩

/-- Multiplying both endpoints by a common right descent preserves a Bruhat comparison. -/
theorem bruhatLE_descent_iff {u w : W} (i : S) (hu : cs.IsRightDescent u i)
    (hw : cs.IsRightDescent w i) :
    cs.BruhatLE u w ↔ cs.BruhatLE (u * cs.simple i) (w * cs.simple i) := by
  constructor
  · intro h
    exact bruhatLE_mul_of_ascent cs (h.mul_simple_of_isRightDescent i hw) i
      (cs.isRightDescent_iff_not_isRightDescent_mul.mp hu)
  · intro h
    simpa only [cs.simple_mul_simple_cancel_right] using
      h.mul_simple_of_not_isRightDescent i
        (cs.isRightDescent_iff_not_isRightDescent_mul.mp hw)

end BruhatIntervals
