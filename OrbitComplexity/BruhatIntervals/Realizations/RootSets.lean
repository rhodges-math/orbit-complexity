import OrbitComplexity.BruhatIntervals.Realizations.Reflections

/-!
# The two root inversion sets

Left inversion roots are the positive roots in the translate of the negative roots, or
equivalently the positive roots whose reflections decrease length on the left. Right inversion
roots are left inversion roots of the inverse element. Both sets have cardinality equal to
Coxeter length.

## Main definitions

* `Realization.rightInversionRoots`: positive roots sent negative by the action.

## Main results

* `Realization.inversionRoots_eq_image`: the intersection with translated negative roots.
* `Realization.inversionRoots_eq_reflections`: the left reflection-length description.
* `Realization.rightInversionRoots_ncard`: right inversion roots count Coxeter length.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- The right inversion roots are the left inversion roots of the inverse group element. -/
def rightInversionRoots (w : W) : Set V := realization.inversionRoots w⁻¹

/-- A positive root is a right inversion root exactly when its image is negative. -/
theorem mem_rightInversionRoots (w : W) (root : V) :
    root ∈ realization.rightInversionRoots w ↔ root ∈ realization.positiveRoots ∧
      -realization.action w root ∈ realization.positiveRoots := by
  simp only [rightInversionRoots, inversionRoots, inv_inv, Set.mem_ofPred_eq]

/-- The left inversion roots are the positive roots in the translate of the negative roots. -/
theorem inversionRoots_eq_image (w : W) :
    realization.inversionRoots w = realization.positiveRoots ∩
      (realization.action w '' (Neg.neg '' realization.positiveRoots)) := by
  ext root
  constructor
  · rintro ⟨hpos, hneg⟩
    refine ⟨hpos, realization.action w⁻¹ root, ?_, realization.action_action_inv w root⟩
    exact ⟨-realization.action w⁻¹ root, hneg, neg_neg _⟩
  · rintro ⟨hpos, negative, ⟨positive, hpositive, rfl⟩, himage⟩
    refine ⟨hpos, ?_⟩
    rw [← himage, realization.action_inv_action, neg_neg]
    exact hpositive

/-- The left inversion roots are exactly the positive roots whose reflections shorten on the
left. -/
theorem inversionRoots_eq_reflections (w : W) :
    realization.inversionRoots w = {root : V | ∃ h : root ∈ realization.positiveRoots,
      cs.length ((realization.rootReflection ⟨root, h⟩).val * w) < cs.length w} := by
  ext root
  constructor
  · intro hroot
    exact ⟨hroot.1, (realization.rootReflection_length_iff w ⟨root, hroot.1⟩).mpr hroot⟩
  · rintro ⟨hpos, hlength⟩
    exact (realization.rootReflection_length_iff w ⟨root, hpos⟩).mp hlength

/-- Right inversion-root sets are finite in every Coxeter group. -/
theorem rightInversionRoots_finite (w : W) : (realization.rightInversionRoots w).Finite :=
  realization.inversionRoots_finite w⁻¹

/-- The right inversion-root cardinality equals Coxeter length. -/
theorem rightInversionRoots_ncard (w : W) :
    (realization.rightInversionRoots w).ncard = cs.length w := by
  rw [rightInversionRoots, realization.inversionRoots_ncard, cs.length_inv]

end BruhatIntervals.Realization
