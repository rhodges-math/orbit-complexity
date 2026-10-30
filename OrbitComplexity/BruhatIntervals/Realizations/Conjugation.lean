import OrbitComplexity.BruhatIntervals.Realizations.Reflections

/-!
# Conjugating root reflections

Conjugating a positive-root reflection gives the reflection in the translated root. Choosing the
positive sign of that translate gives the corresponding positive-root label.

## Main results

* `Realization.action_conjugate_root`: conjugation acts by the translated reflection formula.
* `Realization.rootReflection_conj`: a positive translate labels the conjugated reflection.
* `Realization.rootReflection_conj_neg`: a negative translate has its negative as the positive
  label.

## Implementation notes

The proof uses invariance of the geometric form and faithfulness of the realization action.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Section 4.4.
-/

namespace BruhatIntervals.Realization

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

/-- Conjugating a root reflection gives the translated geometric reflection formula. -/
theorem action_conjugate_root (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) (y : V) :
    realization.action (w * (realization.rootReflection root).val * w⁻¹) y =
      y - (2 * realization.form (realization.action w root.val) y) •
        realization.action w root.val := by
  have hpair : realization.form root.val (realization.action (w⁻¹) y) =
      realization.form (realization.action w root.val) y := by
    have h := realization.action_form w root.val (realization.action (w⁻¹) y)
    rw [realization.action_action_inv] at h
    exact h.symm
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    realization.rootReflection_apply, map_sub, map_smul, realization.action_action_inv, hpair]

/-- A positive translated root has the conjugated Coxeter reflection. -/
theorem rootReflection_conj (w : W)
    (root : {x : V // x ∈ realization.positiveRoots})
    (hpos : realization.action w root.val ∈ realization.positiveRoots) :
    (realization.rootReflection ⟨realization.action w root.val, hpos⟩).val =
      w * (realization.rootReflection root).val * w⁻¹ := by
  apply realization.action_injective
  apply LinearEquiv.ext
  intro y
  rw [realization.rootReflection_apply, realization.action_conjugate_root]

/-- The negative of a negative translated root has the conjugated Coxeter reflection. -/
theorem rootReflection_conj_neg (w : W)
    (root : {x : V // x ∈ realization.positiveRoots})
    (hneg : -realization.action w root.val ∈ realization.positiveRoots) :
    (realization.rootReflection ⟨-realization.action w root.val, hneg⟩).val =
      w * (realization.rootReflection root).val * w⁻¹ := by
  apply realization.action_injective
  apply LinearEquiv.ext
  intro y
  rw [realization.rootReflection_apply, realization.action_conjugate_root,
    LinearMap.BilinForm.neg_left]
  simp only [mul_neg, neg_smul, smul_neg, neg_neg]

end BruhatIntervals.Realization
