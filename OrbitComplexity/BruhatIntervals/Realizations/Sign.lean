import OrbitComplexity.BruhatIntervals.Realizations.Alternating
import OrbitComplexity.BruhatIntervals.Words.Alternating
import OrbitComplexity.BruhatIntervals.Words.Parabolic

/-!
# Root signs and Coxeter length

An element sends a simple root to a positive root exactly when the corresponding simple generator
is a right ascent. Every root therefore has exactly one sign, and every realization is faithful.

## Main results

* `Realization.action_simpleRoot_positive_iff`: root positivity is equivalent to a right ascent.
* `Realization.root_sign`: every root is positive or the negative of a positive root.
* `Realization.action_injective`: the realization action is faithful.

## Implementation notes

The positivity proof is induction on Coxeter length. A two-generator parabolic decomposition
reduces each step to the nonnegative coefficients of an alternating word, without a finiteness
assumption on the group or its set of simple indices.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Theorem 4.2.5 and Corollary 4.2.6.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- A right ascent sends its simple root to a positive root. -/
theorem action_simpleRoot_positive (w : W) (i : Index)
    (hascent : ¬ cs.IsRightDescent w i) :
    realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots := by
  suffices h : ∀ n : ℕ, ∀ w : W, cs.length w = n → ∀ i : Index,
      ¬ cs.IsRightDescent w i →
        realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots from
    h (cs.length w) w rfl i hascent
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen i hascent
    by_cases hw : w = 1
    · subst w
      rw [map_one]
      exact realization.simpleRoot_mem_positiveRoots i
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    obtain ⟨⟨u, v⟩, ⟨hu, hv, hprod, hlength⟩, _⟩ :=
      right_parabolic_decomposition cs ({i, j} : Set Index) w
    change cs.length w = cs.length u + cs.length v at hlength
    have hui : ¬ cs.IsRightDescent u i := cs.isMinimalCosetRep_iff.mp hu i (by simp)
    have huj : ¬ cs.IsRightDescent u j := cs.isMinimalCosetRep_iff.mp hu j (by simp)
    have hvsi : v * cs.simple i ∈ cs.parabolic ({i, j} : Set Index) :=
      mul_mem hv (cs.simple_mem_parabolic (by simp))
    have hvinot : ¬ cs.IsRightDescent v i := by
      intro hdi
      apply hascent
      change cs.length (w * cs.simple i) < cs.length w
      rw [hprod, mul_assoc, cs.length_mul_of_isMinimalCosetRep hu hvsi,
        cs.length_mul_of_isMinimalCosetRep hu hv]
      exact Nat.add_lt_add_left hdi _
    have hvne : v ≠ 1 := by
      intro heq
      apply huj
      simpa only [hprod, heq, mul_one] using hj
    have hvlen : 0 < cs.length v := Nat.pos_of_ne_zero
      (fun hz => hvne (cs.length_eq_zero_iff.mp hz))
    have hult : cs.length u < n := by omega
    have hpi := (ih (cs.length u) hult u rfl i hui).2
    have hpj := (ih (cs.length u) hult u rfl j huj).2
    obtain ⟨word, hred, hletters, hword⟩ :=
      cs.exists_isReduced_wordProd_eq_of_mem_parabolic hv
    have hletterpair : ∀ a ∈ word, a = i ∨ a = j := by simpa using hletters
    have hwasc : ¬ cs.IsRightDescent (cs.wordProd word) i := by rwa [hword]
    have halternating := reduced_word_eq_alternating cs i j hred hletterpair hwasc
    have hbound : matrix i j = 0 ∨ word.length < matrix i j := by
      by_cases hz : matrix i j = 0
      · exact Or.inl hz
      · exact Or.inr (alternating_length_lt cs i j hred hletterpair hwasc hz)
    obtain ⟨a, b, ha, hb, hcoeff⟩ :=
      realization.alternatingRoot_nonneg i j word.length hbound
    have haltprod : cs.wordProd (CoxeterSystem.alternatingWord i j word.length) = v := by
      rw [← halternating, hword]
    rw [haltprod] at hcoeff
    refine ⟨realization.action_mem_roots _ (realization.simpleRoot_mem_roots i), ?_⟩
    rw [hprod, map_mul, LinearEquiv.mul_apply, hcoeff, map_add, map_smul, map_smul]
    exact realization.positiveCone_add
      (realization.positiveCone_smul ha hpi) (realization.positiveCone_smul hb hpj)

/-- A right descent sends its simple root to a negative root. -/
theorem action_simpleRoot_negative (w : W) (i : Index)
    (hdesc : cs.IsRightDescent w i) :
    -realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots := by
  have hpos := realization.action_simpleRoot_positive (w * cs.simple i) i
    (cs.isRightDescent_iff_not_isRightDescent_mul.mp hdesc)
  simpa only [map_mul, LinearEquiv.mul_apply, realization.action_simple_root, map_neg] using hpos

/-- The image of a simple root is positive exactly when its simple generator is a right ascent. -/
theorem action_simpleRoot_positive_iff (w : W) (i : Index) :
    realization.action w (realization.simpleRoot i) ∈ realization.positiveRoots ↔
      ¬ cs.IsRightDescent w i := by
  constructor
  · intro hpos hdesc
    exact realization.positiveRoots_ne_neg hpos
      (realization.action_simpleRoot_negative w i hdesc)
  · exact realization.action_simpleRoot_positive w i

/-- Every root is positive or the negative of a positive root. -/
theorem root_sign {x : V} (hx : x ∈ realization.roots) :
    x ∈ realization.positiveRoots ∨ -x ∈ realization.positiveRoots := by
  obtain ⟨w, i, rfl⟩ := hx
  by_cases hdesc : cs.IsRightDescent w i
  · exact Or.inr (realization.action_simpleRoot_negative w i hdesc)
  · exact Or.inl (realization.action_simpleRoot_positive w i hdesc)

/-- Every realization action is faithful. -/
theorem action_injective : Function.Injective realization.action := by
  have hkernel : ∀ g : W, realization.action g = 1 → g = 1 := by
    intro g haction
    by_contra hne
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hne
    have hneg := realization.action_simpleRoot_negative g i hi
    have hfix : realization.action g (realization.simpleRoot i) = realization.simpleRoot i := by
      rw [haction]
      rfl
    rw [hfix] at hneg
    exact realization.positiveRoots_ne_neg (realization.simpleRoot_mem_positiveRoots i) hneg
  intro w v heq
  apply mul_inv_eq_one.mp
  apply hkernel
  rw [map_mul, map_inv, heq, mul_inv_cancel]

end BruhatIntervals.Realization
