import OrbitComplexity.BruhatIntervals.Realizations.Sign
import Mathlib.Data.Set.Card

/-!
# Positive roots and inversion sets

A simple reflection permutes the positive roots other than its own simple root. The left inversion
set consists of the positive roots made negative by the inverse action. Each right ascent inserts
one new root, so the inversion set is finite and its cardinality is Coxeter length.

## Main definitions

* `Realization.inversionRoots`: positive roots sent negative by the inverse action.

## Main results

* `Realization.action_simple_positive`: simple reflections preserve the other positive roots.
* `Realization.inversionRoots_mul_simple`: a right ascent inserts its new positive root.
* `Realization.inversionRoots_finite`: inversion sets are finite for every Coxeter group.
* `Realization.inversionRoots_ncard`: the inversion-root cardinality equals Coxeter length.

## Implementation notes

No finiteness hypothesis is placed on the group or the simple indices. Finiteness of each
inversion set is proved together with its cardinality by length induction.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem eq_simple_of_neg_action (i : Index) {x : V}
    (hx : x ∈ realization.positiveRoots)
    (hneg : -realization.action (cs.simple i) x ∈ realization.positiveRoots) :
    x = realization.simpleRoot i := by
  obtain ⟨f, hfnonneg, hfx⟩ := hx.2
  obtain ⟨g, hgnonneg, hgx⟩ := hneg.2
  have hsum : f + g = Finsupp.single i (2 * realization.form (realization.simpleRoot i) x) :=
    realization.root_independent (by
      rw [map_add, hfx, hgx, Finsupp.linearCombination_single, realization.action_simple]
      module)
  have hf : f = Finsupp.single i (f i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.single_eq_same]
    have hcoord := congrArg (fun coefficients : Index →₀ ℝ => coefficients j) hsum
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hji] at hcoord ⊢
    have hfj := hfnonneg j
    have hgj := hgnonneg j
    linarith
  have hxscalar : x = (f i) • realization.simpleRoot i := by
    rw [hf, Finsupp.linearCombination_single] at hfx
    exact hfx.symm
  have hunit := realization.form_root_eq_one hx.1
  rw [hxscalar, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    realization.form_root_self, mul_one] at hunit
  have hfone : f i = 1 := by
    have hfi := hfnonneg i
    nlinarith
  simpa only [hfone, one_smul] using hxscalar

/-- A simple reflection sends every other positive root to a positive root. -/
theorem action_simple_positive (i : Index) {x : V}
    (hx : x ∈ realization.positiveRoots) (hne : x ≠ realization.simpleRoot i) :
    realization.action (cs.simple i) x ∈ realization.positiveRoots := by
  rcases realization.root_sign (realization.action_mem_roots _ hx.1) with hpos | hneg
  · exact hpos
  · exact False.elim (hne (eq_simple_of_neg_action realization i hx hneg))

/-- The inverse group element reverses the realization action. -/
theorem action_inv_action (w : W) (x : V) :
    realization.action (w⁻¹) (realization.action w x) = x := by
  rw [map_inv]
  exact (realization.action w).symm_apply_apply x

/-- The group element reverses the action of its inverse. -/
theorem action_action_inv (w : W) (x : V) :
    realization.action w (realization.action (w⁻¹) x) = x := by
  rw [map_inv]
  exact (realization.action w).apply_symm_apply x

/-- The left inversion roots are positive roots made negative by the inverse action. -/
def inversionRoots (w : W) : Set V :=
  {x | x ∈ realization.positiveRoots ∧
    -realization.action (w⁻¹) x ∈ realization.positiveRoots}

/-- The identity has no inversion roots. -/
theorem inversionRoots_one : realization.inversionRoots 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hpos, hneg⟩ := hx
  rw [inv_one, map_one] at hneg
  exact realization.positiveRoots_ne_neg hpos hneg

/-- A translated simple root does not belong to the inversion set of its translator. -/
theorem action_root_not_inversions (w : W) (i : Index) :
    realization.action w (realization.simpleRoot i) ∉ realization.inversionRoots w := by
  intro hx
  have hneg := hx.2
  rw [realization.action_inv_action] at hneg
  exact realization.positiveRoots_ne_neg (realization.simpleRoot_mem_positiveRoots i) hneg

/-- Right multiplication at an ascent inserts its new positive root into the inversion set. -/
theorem inversionRoots_mul_simple (w : W) (i : Index)
    (hascent : ¬ cs.IsRightDescent w i) :
    realization.inversionRoots (w * cs.simple i) =
      insert (realization.action w (realization.simpleRoot i)) (realization.inversionRoots w) := by
  have hnewpos := realization.action_simpleRoot_positive w i hascent
  ext x
  have hinv : realization.action ((w * cs.simple i)⁻¹) x =
      realization.action (cs.simple i) (realization.action (w⁻¹) x) := by
    rw [mul_inv_rev, cs.inv_simple, map_mul, LinearEquiv.mul_apply]
  constructor
  · intro hx
    change x ∈ realization.positiveRoots ∧
      -realization.action ((w * cs.simple i)⁻¹) x ∈ realization.positiveRoots at hx
    rw [hinv] at hx
    rcases realization.root_sign (realization.action_mem_roots (w⁻¹) hx.1.1) with hpos | hneg
    · have heq : realization.action (w⁻¹) x = realization.simpleRoot i := by
        by_contra hne
        exact realization.positiveRoots_ne_neg
          (realization.action_simple_positive i hpos hne) hx.2
      apply Set.mem_insert_iff.mpr
      left
      have h := congrArg (fun y => realization.action w y) heq
      rwa [realization.action_action_inv] at h
    · exact Set.mem_insert_of_mem _ ⟨hx.1, hneg⟩
  · intro hx
    rcases Set.mem_insert_iff.mp hx with hxeq | hx
    · subst x
      refine ⟨hnewpos, ?_⟩
      rw [hinv, realization.action_inv_action, realization.action_simple_root, neg_neg]
      exact realization.simpleRoot_mem_positiveRoots i
    · refine ⟨hx.1, ?_⟩
      rw [hinv]
      have hne : -realization.action (w⁻¹) x ≠ realization.simpleRoot i := by
        intro heq
        have h := congrArg (fun y => realization.action w y) heq
        rw [map_neg, realization.action_action_inv] at h
        have hxneg : -x ∈ realization.positiveRoots := by rw [h]; exact hnewpos
        exact realization.positiveRoots_ne_neg hx.1 hxneg
      simpa only [map_neg] using realization.action_simple_positive i hx.2 hne

private theorem inversionRoots_finite_card (w : W) :
    (realization.inversionRoots w).Finite ∧
      (realization.inversionRoots w).ncard = cs.length w := by
  suffices h : ∀ n : ℕ, ∀ w : W, cs.length w = n →
      (realization.inversionRoots w).Finite ∧ (realization.inversionRoots w).ncard = n from
    h (cs.length w) w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen
    by_cases hw : w = 1
    · subst w
      simp only [cs.length_one] at hlen
      subst n
      rw [realization.inversionRoots_one]
      exact ⟨Set.finite_empty, Set.ncard_empty V⟩
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
    have hlenv : cs.length (w * cs.simple i) + 1 = n := by
      simpa only [hlen] using cs.isRightDescent_iff.mp hi
    have hind := ih (cs.length (w * cs.simple i)) (by omega) (w * cs.simple i) rfl
    have hstep := realization.inversionRoots_mul_simple (w * cs.simple i) i
      (cs.isRightDescent_iff_not_isRightDescent_mul.mp hi)
    rw [cs.simple_mul_simple_cancel_right] at hstep
    constructor
    · rw [hstep]
      exact hind.1.insert _
    · rw [hstep, Set.ncard_insert_of_notMem
        (realization.action_root_not_inversions (w * cs.simple i) i) hind.1, hind.2]
      exact hlenv

/-- The inversion-root set of each element is finite. -/
theorem inversionRoots_finite (w : W) : (realization.inversionRoots w).Finite :=
  (inversionRoots_finite_card realization w).1

/-- The number of inversion roots equals Coxeter length. -/
theorem inversionRoots_ncard (w : W) :
    (realization.inversionRoots w).ncard = cs.length w :=
  (inversionRoots_finite_card realization w).2

end BruhatIntervals.Realization
