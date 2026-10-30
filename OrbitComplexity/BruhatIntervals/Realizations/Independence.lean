import OrbitComplexity.BruhatIntervals.Realizations.Reflections
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Independence of positive root pairs

Two distinct positive roots are linearly independent. Unit root lengths reduce collinearity to
equality or opposite signs, and the pointed positive cone excludes the latter possibility.

## Main results

* `Realization.positiveRoots_pair_independent`: distinct positive roots form an independent pair.
* `Realization.positiveRoots_pair_finrank`: their real span has dimension two.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- Distinct positive roots are linearly independent, including for a degenerate root form. -/
theorem positiveRoots_pair_independent
    (α β : {x : V // x ∈ realization.positiveRoots}) (hne : α ≠ β) :
    LinearIndependent ℝ ![α.val, β.val] := by
  rw [linearIndependent_fin2]
  refine ⟨realization.root_ne_zero β.property.1, ?_⟩
  intro a heq
  change a • β.val = α.val at heq
  have hunit := realization.form_root_eq_one α.property.1
  rw [← heq, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    realization.form_root_eq_one β.property.1, mul_one] at hunit
  rcases mul_self_eq_one_iff.mp hunit with hpos | hneg
  · apply hne
    apply Subtype.ext
    simpa only [hpos, one_smul] using heq.symm
  · have hcol : α.val = -β.val := by simpa only [hneg, neg_one_smul] using heq.symm
    have hnegative : -α.val ∈ realization.positiveRoots := by
      rw [hcol, neg_neg]
      exact β.property
    exact realization.positiveRoots_ne_neg α.property hnegative

/-- The real span of two distinct positive roots has dimension two. -/
theorem positiveRoots_pair_finrank
    (α β : {x : V // x ∈ realization.positiveRoots}) (hne : α ≠ β) :
    Module.finrank ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) = 2 := by
  have h := finrank_span_eq_card (positiveRoots_pair_independent realization α β hne)
  have hrange : Set.range (![α.val, β.val] : Fin 2 → V) = {α.val, β.val} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      · rcases hx with rfl
        exact ⟨1, rfl⟩
  rw [hrange] at h
  simpa only [Fintype.card_fin] using h

end BruhatIntervals.Realization
