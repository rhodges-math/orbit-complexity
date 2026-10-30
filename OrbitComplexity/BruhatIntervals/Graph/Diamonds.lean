import OrbitComplexity.BruhatIntervals.Order.Basic
import Mathlib.Order.Cover

/-! # Strong and weak Bruhat diamonds

A simple-reflection edge and a distinct reflection edge with the same upper or lower
vertex complete a diamond. Covers use the intrinsic Bruhat partial order.

## Main results

* `strong_weak_diamond`: both orientations of the diamond follow from the lifting property.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private theorem step_lt {u v : W} (h : cs.BruhatStep u v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u < v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  apply lt_of_le_of_ne h.bruhatLE
  intro heq
  have hlt := h.length_lt
  rw [heq] at hlt
  exact lt_irrefl _ hlt

private theorem descent_cover (w : W) (i : S) (hw : cs.IsRightDescent w i) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w * cs.simple i ⋖ w := by
  let : PartialOrder W := cs.bruhatPartialOrder
  refine ⟨step_lt cs (cs.bruhatStep_mul_simple_of_isRightDescent i hw), ?_⟩
  intro z hlow hhigh
  have hfirst := (show cs.BruhatLE (w * cs.simple i) z from hlow.le).length_lt_of_ne
    hlow.ne
  have hsecond := (show cs.BruhatLE z w from hhigh.le).length_lt_of_ne hhigh.ne
  have hlength := cs.isRightDescent_iff.mp hw
  omega

private theorem ascent_descent (w : W) (i : S) (hw : ¬ cs.IsRightDescent w i) :
    cs.IsRightDescent (w * cs.simple i) i := by
  apply cs.isRightDescent_iff.mpr
  simpa only [cs.simple_mul_simple_cancel_right] using
    (cs.not_isRightDescent_iff.mp hw).symm

private theorem ascent_cover (w : W) (i : S) (hw : ¬ cs.IsRightDescent w i) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w ⋖ w * cs.simple i := by
  simpa only [cs.simple_mul_simple_cancel_right] using
    descent_cover cs (w * cs.simple i) i (ascent_descent cs w i hw)

private theorem cover_descents {u v : W} (i : S) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ v → cs.IsRightDescent u i → cs.IsRightDescent v i →
      u * cs.simple i ⋖ v * cs.simple i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro h hu hv
  have hle := (bruhatLE_descent_iff cs i hu hv).mp h.le
  have hne : u * cs.simple i ≠ v * cs.simple i := fun heq => h.lt.ne (mul_right_cancel heq)
  have hvas := cs.isRightDescent_iff_not_isRightDescent_mul.mp hv
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro z hlow hhigh
  by_cases hz : cs.IsRightDescent z i
  · have huz : cs.BruhatLE u z := by
      simpa only [cs.simple_mul_simple_cancel_right] using
        (show cs.BruhatLE (u * cs.simple i) z from hlow.le).mul_simple_of_isRightDescent
          i hz
    have huv : u ≤ v * cs.simple i := huz.trans hhigh.le
    rcases h.eq_or_eq huv (descent_cover cs v i hv).le with heq | heq
    · rw [heq] at hvas
      exact hvas hu
    · exact (descent_cover cs v i hv).lt.ne heq
  · have huz : cs.BruhatLE u (z * cs.simple i) := by
      simpa only [cs.simple_mul_simple_cancel_right] using
        (show cs.BruhatLE (u * cs.simple i) z from hlow.le).mul_simple_of_not_isRightDescent
          i hz
    have hzv : cs.BruhatLE (z * cs.simple i) v := by
      simpa only [cs.simple_mul_simple_cancel_right] using
        (show cs.BruhatLE z (v * cs.simple i) from hhigh.le).mul_simple_of_not_isRightDescent
          i hvas
    rcases h.eq_or_eq huz hzv with heq | heq
    · have hzu : z = u * cs.simple i := by
        calc
          z = z * cs.simple i * cs.simple i :=
            (cs.simple_mul_simple_cancel_right (w := z) i).symm
          _ = u * cs.simple i := congrArg (fun a => a * cs.simple i) heq
      exact hlow.ne hzu.symm
    · have hzv' : z = v * cs.simple i := by
        calc
          z = z * cs.simple i * cs.simple i :=
            (cs.simple_mul_simple_cancel_right (w := z) i).symm
          _ = v * cs.simple i := congrArg (fun a => a * cs.simple i) heq
      exact hhigh.ne hzv'

private theorem cover_ascents {u v : W} (i : S) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ v → ¬ cs.IsRightDescent u i → ¬ cs.IsRightDescent v i →
      u * cs.simple i ⋖ v * cs.simple i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro h hu hv
  have hle := (show cs.BruhatLE u v from h.le).mul_simple_of_not_isRightDescent i hv
  have hne : u * cs.simple i ≠ v * cs.simple i := fun heq => h.lt.ne (mul_right_cancel heq)
  have hud := ascent_descent cs u i hu
  have hvd := ascent_descent cs v i hv
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro z hlow hhigh
  by_cases hz : cs.IsRightDescent z i
  · have huz := (bruhatLE_descent_iff cs i hud hz).mp hlow.le
    have hzv := (bruhatLE_descent_iff cs i hz hvd).mp hhigh.le
    simp only [cs.simple_mul_simple_cancel_right] at huz hzv
    rcases h.eq_or_eq huz hzv with heq | heq
    · have hzu : z = u * cs.simple i := by
        calc
          z = z * cs.simple i * cs.simple i :=
            (cs.simple_mul_simple_cancel_right (w := z) i).symm
          _ = u * cs.simple i := congrArg (fun a => a * cs.simple i) heq
      exact hlow.ne hzu.symm
    · have hzv' : z = v * cs.simple i := by
        calc
          z = z * cs.simple i * cs.simple i :=
            (cs.simple_mul_simple_cancel_right (w := z) i).symm
          _ = v * cs.simple i := congrArg (fun a => a * cs.simple i) heq
      exact hhigh.ne hzv'
  · have hzv : cs.BruhatLE z v := by
      simpa only [cs.simple_mul_simple_cancel_right] using
        bruhatLE_mul_of_ascent cs hhigh.le i hz
    have huv : u * cs.simple i ≤ v := hlow.le.trans hzv
    rcases h.eq_or_eq (ascent_cover cs u i hu).le huv with heq | heq
    · exact (ascent_cover cs u i hu).lt.ne heq.symm
    · rw [heq] at hud
      exact hv hud

private theorem downward_diamond (w t : W) (i : S) :
    let : PartialOrder W := cs.bruhatPartialOrder
    (w * cs.simple i ⋖ w) → (t * w ⋖ w) → w * cs.simple i ≠ t * w →
      (t * w * cs.simple i ⋖ w * cs.simple i) ∧ (t * w * cs.simple i ⋖ t * w) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hsimple href hne
  have hw : cs.IsRightDescent w i :=
    (show cs.BruhatLE (w * cs.simple i) w from hsimple.le).length_lt_of_ne hsimple.lt.ne
  have ht : cs.IsRightDescent (t * w) i := by
    by_contra hnot
    have hle := (lifting_property cs ⟨href.le, href.lt.ne⟩ i hw hnot).1
    rcases href.eq_or_eq hle hsimple.le with heq | heq
    · exact hne heq
    · exact hsimple.lt.ne heq
  exact ⟨cover_descents cs i href ht hw, descent_cover cs (t * w) i ht⟩

/-- A simple-reflection edge and a distinct reflection edge complete a Bruhat diamond in either
orientation, using the intrinsic partial-order cover relation. -/
theorem strong_weak_diamond (w t : W) (i : S) (ht : cs.IsReflection t) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ((w * cs.simple i ⋖ w) → (t * w ⋖ w) → w * cs.simple i ≠ t * w →
      (t * w * cs.simple i ⋖ w * cs.simple i) ∧ (t * w * cs.simple i ⋖ t * w)) ∧
    ((w ⋖ w * cs.simple i) → (w ⋖ t * w) → w * cs.simple i ≠ t * w →
      (w * cs.simple i ⋖ t * w * cs.simple i) ∧ (t * w ⋖ t * w * cs.simple i)) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  refine ⟨downward_diamond cs w t i, ?_⟩
  intro hsimple href hne
  have hw : ¬ cs.IsRightDescent w i := by
    intro hdesc
    exact (not_lt_of_ge hsimple.le) (descent_cover cs w i hdesc).lt
  have htw : ¬ cs.IsRightDescent (t * w) i := by
    intro hdesc
    have hneq : t * w * cs.simple i ≠ t * (t * w) := by
      rw [← mul_assoc, ht.mul_self, one_mul]
      intro heq
      apply hne
      have h := congrArg (fun a => a * cs.simple i) heq
      simpa only [cs.simple_mul_simple_cancel_right] using h.symm
    have hdiamond := downward_diamond cs (t * w) t i
      (descent_cover cs (t * w) i hdesc) (by
        simpa only [← mul_assoc, ht.mul_self, one_mul] using href) hneq
    have hcontrad : w * cs.simple i ⋖ w := by
      simpa only [← mul_assoc, ht.mul_self, one_mul] using hdiamond.2
    exact (not_lt_of_ge hsimple.le) hcontrad.lt
  exact ⟨cover_ascents cs i href hw htw, ascent_cover cs (t * w) i htw⟩

end BruhatIntervals
