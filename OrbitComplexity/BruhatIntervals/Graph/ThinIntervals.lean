import OrbitComplexity.BruhatIntervals.Order.Covers

/-! # Rank-two Bruhat intervals

Every interval formed by two consecutive covers has exactly two middle vertices.
Right multiplication by a common descent gives a piecewise equivalence between the
middle vertices; when the lower endpoint has an ascent, the two middles are explicit.

## Main results

* `bruhat_rank_two_diamond`: there is a unique middle vertex distinct from a chosen one.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.7, Lemma 2.7.3.
-/

namespace BruhatIntervals

variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private def middle (z y w : W) : Prop :=
  cs.BruhatLE z w ∧ cs.BruhatLE w y ∧ cs.length w = cs.length z + 1

private theorem eq_of_length {a b : W} (h : cs.BruhatLE a b)
    (hlen : cs.length a = cs.length b) : a = b := by
  by_contra hne
  have hlt := h.length_lt_of_ne hne
  omega

private noncomputable def middleUp (z y w : W) (i : S) : W := by
  classical
  exact if w = z then y * cs.simple i else w * cs.simple i

private noncomputable def middleDown (z y w : W) (i : S) : W := by
  classical
  exact if w = y * cs.simple i then z else w * cs.simple i

private theorem middleUp_mem (z y w : W) (i : S)
    (hz : cs.IsRightDescent z i) (hy : cs.IsRightDescent y i)
    (hlen : cs.length y = cs.length z + 2)
    (hw : middle cs (z * cs.simple i) (y * cs.simple i) w) :
    middle cs z y (middleUp cs z y w i) := by
  classical
  have hzl := cs.isRightDescent_iff.mp hz
  have hyl := cs.isRightDescent_iff.mp hy
  have hwl : cs.length w = cs.length z := by have := hw.2.2; omega
  have hya := cs.isRightDescent_iff_not_isRightDescent_mul.mp hy
  by_cases heq : w = z
  · simp only [middleUp, ite_eq_left heq]
    refine ⟨?_, (cs.bruhatStep_mul_simple_of_isRightDescent i hy).bruhatLE, by omega⟩
    simpa only [heq] using hw.2.1
  · simp only [middleUp, ite_eq_right heq]
    have hwa : ¬ cs.IsRightDescent w i := by
      intro hwd
      have hzw : cs.BruhatLE z w := by
        simpa only [cs.simple_mul_simple_cancel_right] using
          hw.1.mul_simple_of_isRightDescent i hwd
      exact heq (eq_of_length cs hzw (by omega)).symm
    refine ⟨?_, ?_, ?_⟩
    · simpa only [cs.simple_mul_simple_cancel_right] using
        hw.1.mul_simple_of_not_isRightDescent i hwa
    · simpa only [cs.simple_mul_simple_cancel_right] using
        hw.2.1.mul_simple_of_not_isRightDescent i hya
    · rw [cs.not_isRightDescent_iff.mp hwa, hwl]

private theorem middleDown_mem (z y w : W) (i : S)
    (hz : cs.IsRightDescent z i) (hy : cs.IsRightDescent y i)
    (hlen : cs.length y = cs.length z + 2) (hw : middle cs z y w) :
    middle cs (z * cs.simple i) (y * cs.simple i) (middleDown cs z y w i) := by
  classical
  have hzl := cs.isRightDescent_iff.mp hz
  have hyl := cs.isRightDescent_iff.mp hy
  by_cases heq : w = y * cs.simple i
  · simp only [middleDown, ite_eq_left heq]
    refine ⟨(cs.bruhatStep_mul_simple_of_isRightDescent i hz).bruhatLE, ?_, by omega⟩
    simpa only [heq] using hw.1
  · simp only [middleDown, ite_eq_right heq]
    have hwd : cs.IsRightDescent w i := by
      by_contra hwa
      have hwy := bruhatLE_mul_of_ascent cs hw.2.1 i hwa
      exact heq (eq_of_length cs hwy (by have := hw.2.2; omega))
    refine ⟨(bruhatLE_descent_iff cs i hz hwd).mp hw.1,
      (bruhatLE_descent_iff cs i hwd hy).mp hw.2.1, ?_⟩
    have hwdl := cs.isRightDescent_iff.mp hwd
    have := hw.2.2
    omega

private theorem middleDown_up (z y w : W) (i : S)
    (hy : cs.IsRightDescent y i)
    (hw : middle cs (z * cs.simple i) (y * cs.simple i) w) :
    middleDown cs z y (middleUp cs z y w i) i = w := by
  classical
  by_cases heq : w = z
  · simp [middleUp, middleDown, heq]
  · have hne : w * cs.simple i ≠ y * cs.simple i := by
      intro heq'
      have hwy : w = y := mul_right_cancel heq'
      have hlen := hw.2.1.length_le
      have hyl := cs.isRightDescent_iff.mp hy
      rw [hwy] at hlen
      omega
    simp only [middleUp, middleDown, ite_eq_right heq, ite_eq_right hne,
      cs.simple_mul_simple_cancel_right]

private theorem middleUp_down (z y w : W) (i : S)
    (hz : cs.IsRightDescent z i) (hw : middle cs z y w) :
    middleUp cs z y (middleDown cs z y w i) i = w := by
  classical
  by_cases heq : w = y * cs.simple i
  · simp [middleUp, middleDown, heq]
  · have hne : w * cs.simple i ≠ z := by
      intro heq'
      have hlen := congrArg cs.length heq'
      have hzl := cs.isRightDescent_iff.mp hz
      have heq'' : w = z * cs.simple i := by
        have h := congrArg (fun a => a * cs.simple i) heq'
        simpa only [cs.simple_mul_simple_cancel_right] using h
      have hwl := hw.2.2
      rw [heq''] at hwl
      omega
    simp only [middleUp, middleDown, ite_eq_right heq, ite_eq_right hne,
      cs.simple_mul_simple_cancel_right]

private noncomputable def middleEquiv (z y : W) (i : S)
    (hz : cs.IsRightDescent z i) (hy : cs.IsRightDescent y i)
    (hlen : cs.length y = cs.length z + 2) :
    {w : W // middle cs (z * cs.simple i) (y * cs.simple i) w} ≃
      {w : W // middle cs z y w} where
  toFun w := ⟨middleUp cs z y w.val i, middleUp_mem cs z y w.val i hz hy hlen w.property⟩
  invFun w := ⟨middleDown cs z y w.val i, middleDown_mem cs z y w.val i hz hy hlen w.property⟩
  left_inv w := Subtype.ext (middleDown_up cs z y w.val i hy w.property)
  right_inv w := Subtype.ext (middleUp_down cs z y w.val i hz w.property)

private theorem two_middle (z y : W) (hle : cs.BruhatLE z y)
    (hlen : cs.length y = cs.length z + 2) :
    ∃ a b : W, a ≠ b ∧ middle cs z y a ∧ middle cs z y b ∧
      ∀ w : W, middle cs z y w ↔ w = a ∨ w = b := by
  classical
  suffices h : ∀ n : ℕ, ∀ z y : W, cs.length y = n → cs.BruhatLE z y →
      cs.length y = cs.length z + 2 →
      ∃ a b : W, a ≠ b ∧ middle cs z y a ∧ middle cs z y b ∧
        ∀ w : W, middle cs z y w ↔ w = a ∨ w = b from
    h (cs.length y) z y rfl hle hlen
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z y hny hle hlen
    have hyne : y ≠ 1 := by
      intro heq
      rw [heq, cs.length_one] at hlen
      omega
    obtain ⟨i, hy⟩ := cs.exists_rightDescent_of_ne_one hyne
    have hyl := cs.isRightDescent_iff.mp hy
    by_cases hz : cs.IsRightDescent z i
    · have hzl := cs.isRightDescent_iff.mp hz
      have hshift := (bruhatLE_descent_iff cs i hz hy).mp hle
      obtain ⟨a, b, hab, ha, hb, hpair⟩ := ih (cs.length (y * cs.simple i)) (by omega)
        (z * cs.simple i) (y * cs.simple i) rfl hshift (by omega)
      let e := middleEquiv cs z y i hz hy hlen
      let aa : {w : W // middle cs (z * cs.simple i) (y * cs.simple i) w} := ⟨a, ha⟩
      let bb : {w : W // middle cs (z * cs.simple i) (y * cs.simple i) w} := ⟨b, hb⟩
      refine ⟨(e aa).val, (e bb).val, ?_, (e aa).property, (e bb).property, ?_⟩
      · intro heq
        exact hab (congrArg Subtype.val (e.injective (Subtype.ext heq)))
      · intro w
        constructor
        · intro hw
          let ww : {w : W // middle cs z y w} := ⟨w, hw⟩
          rcases (hpair (e.symm ww).val).mp (e.symm ww).property with heq | heq
          · left
            have heq' : e.symm ww = aa := Subtype.ext heq
            have h := congrArg (fun p => (e p).val) heq'
            simpa only [Equiv.apply_symm_apply] using h
          · right
            have heq' : e.symm ww = bb := Subtype.ext heq
            have h := congrArg (fun p => (e p).val) heq'
            simpa only [Equiv.apply_symm_apply] using h
        · rintro (rfl | rfl)
          · exact (e aa).property
          · exact (e bb).property
    · have hzl := cs.not_isRightDescent_iff.mp hz
      have ha : middle cs z y (z * cs.simple i) := by
        refine ⟨?_, hle.mul_simple_of_isRightDescent i hy, hzl⟩
        exact (cs.bruhatStep_mul_simple i (hzl ▸ Nat.lt_succ_self _)).bruhatLE
      have hb : middle cs z y (y * cs.simple i) :=
        ⟨bruhatLE_mul_of_ascent cs hle i hz,
          (cs.bruhatStep_mul_simple_of_isRightDescent i hy).bruhatLE, by omega⟩
      refine ⟨z * cs.simple i, y * cs.simple i, ?_, ha, hb, ?_⟩
      · intro heq
        have hzy : z = y := mul_right_cancel heq
        rw [hzy] at hlen
        omega
      · intro w
        constructor
        · intro hw
          by_cases hwd : cs.IsRightDescent w i
          · left
            have hzw := hw.1.mul_simple_of_isRightDescent i hwd
            exact (eq_of_length cs hzw (by have := hw.2.2; omega)).symm
          · right
            have hwy := bruhatLE_mul_of_ascent cs hw.2.1 i hwd
            exact eq_of_length cs hwy (by have := hw.2.2; omega)
        · rintro (rfl | rfl)
          · exact ha
          · exact hb

/-- A two-cover Bruhat interval has a unique middle vertex other than the specified one. -/
theorem bruhat_rank_two_diamond (z x y : W) :
    let : PartialOrder W := cs.bruhatPartialOrder
    z ⋖ x → x ⋖ y → ∃! other : W, other ≠ x ∧ z ⋖ other ∧ other ⋖ y := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hzx hxy
  have hfirst := (bruhat_covBy_iff cs z x).mp hzx
  have hsecond := (bruhat_covBy_iff cs x y).mp hxy
  have hlen : cs.length y = cs.length z + 2 := by omega
  obtain ⟨a, b, hab, ha, hb, hpair⟩ := two_middle cs z y (hzx.le.trans hxy.le) hlen
  have hxa : x = a ∨ x = b := (hpair x).mp ⟨hzx.le, hxy.le, hfirst.2⟩
  have hcov (w : W) (hw : middle cs z y w) : z ⋖ w ∧ w ⋖ y :=
    ⟨(bruhat_covBy_iff cs z w).mpr ⟨hw.1, hw.2.2⟩,
      (bruhat_covBy_iff cs w y).mpr ⟨hw.2.1, by have := hw.2.2; omega⟩⟩
  rcases hxa with rfl | rfl
  · refine ⟨b, ⟨hab.symm, (hcov b hb).1, (hcov b hb).2⟩, ?_⟩
    rintro other ⟨hne, hzo, hoy⟩
    have ho := (hpair other).mp ⟨hzo.le, hoy.le, ((bruhat_covBy_iff cs z other).mp hzo).2⟩
    exact ho.resolve_left hne
  · refine ⟨a, ⟨hab, (hcov a ha).1, (hcov a ha).2⟩, ?_⟩
    rintro other ⟨hne, hzo, hoy⟩
    have ho := (hpair other).mp ⟨hzo.le, hoy.le, ((bruhat_covBy_iff cs z other).mp hzo).2⟩
    exact ho.resolve_right hne

end BruhatIntervals
