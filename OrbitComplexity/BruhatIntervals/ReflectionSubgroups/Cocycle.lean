import OrbitComplexity.BruhatIntervals.Realizations.Conjugation

/-!
# The reflection-inversion cocycle

The reflection inversions of a product are the symmetric difference of the first factor's
inversions and the conjugates of the second factor's inversions. The pointwise formula is valid
for every element, including elements that are not reflections.

## Main results

* `leftInversion_mul_iff`: product inversion membership is exclusive-or of the two memberships.

## Implementation notes

The geometric realization proves the formula for every Coxeter system. Root-sign partition and
the conjugation formula account for the two possible signs of the intermediate root.

## References

* M. Dyer, *Reflection Subgroups of Coxeter Systems*, Journal of Algebra 135 (1990),
  Sections 2 and 3.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]

private theorem leftInv_root (realization : Realization cs (V := V)) (w : W)
    (root : {x : V // x ∈ realization.positiveRoots}) :
    cs.IsLeftInversion w (realization.rootReflection root).val ↔
      -realization.action (w⁻¹) root.val ∈ realization.positiveRoots := by
  rw [realization.rootReflection_leftInversion_iff]
  exact and_iff_right root.property

private theorem neg_positive_iff (realization : Realization cs (V := V)) {x : V}
    (hx : x ∈ realization.roots) :
    -x ∈ realization.positiveRoots ↔ x ∉ realization.positiveRoots := by
  constructor
  · intro hneg hpos
    exact realization.positiveRoots_ne_neg hpos hneg
  · intro hnot
    exact (realization.root_sign hx).resolve_left hnot

private theorem inversion_mul_iff (realization : Realization cs (V := V)) (u v t : W) :
    cs.IsLeftInversion (u * v) t ↔
      Xor (cs.IsLeftInversion u t) (cs.IsLeftInversion v (u⁻¹ * t * u)) := by
  by_cases ht : cs.IsReflection t
  · obtain ⟨root, hroot⟩ := realization.rootReflection_surjective ⟨t, ht⟩
    have heq : (realization.rootReflection root).val = t := congrArg Subtype.val hroot
    let β := realization.action (u⁻¹) root.val
    have hβroot : β ∈ realization.roots := realization.action_mem_roots (u⁻¹) root.property.1
    rcases realization.root_sign hβroot with hpos | hneg
    · have hconj : (realization.rootReflection ⟨β, hpos⟩).val = u⁻¹ * t * u := by
        simpa only [heq, inv_inv] using realization.rootReflection_conj (u⁻¹) root hpos
      have hnotu : ¬ cs.IsLeftInversion u t := by
        rw [← heq, leftInv_root]
        exact fun hnegative => realization.positiveRoots_ne_neg hpos hnegative
      have hmain : cs.IsLeftInversion (u * v) t ↔
          cs.IsLeftInversion v (u⁻¹ * t * u) := by
        rw [← hconj, ← heq, leftInv_root, leftInv_root, mul_inv_rev, map_mul,
          LinearEquiv.mul_apply]
      simpa only [Xor, hnotu, not_false_eq_true, false_and, false_or, and_true] using hmain
    · have hconj : (realization.rootReflection ⟨-β, hneg⟩).val = u⁻¹ * t * u := by
        simpa only [heq, inv_inv] using realization.rootReflection_conj_neg (u⁻¹) root hneg
      have hu : cs.IsLeftInversion u t := by
        rw [← heq, leftInv_root]
        exact hneg
      have hmain : cs.IsLeftInversion (u * v) t ↔
          ¬ cs.IsLeftInversion v (u⁻¹ * t * u) := by
        rw [← hconj, ← heq, leftInv_root, leftInv_root, map_neg, neg_neg,
          mul_inv_rev, map_mul, LinearEquiv.mul_apply]
        exact neg_positive_iff realization (realization.action_mem_roots (v⁻¹) hβroot)
      simpa only [Xor, hu, not_true_eq_false, true_and, and_false, or_false] using hmain
  · have hconj : ¬ cs.IsReflection (u⁻¹ * t * u) := by
      intro h
      apply ht
      apply (cs.isReflection_conj_iff (u⁻¹) t).mp
      simpa only [inv_inv] using h
    simp only [CoxeterSystem.IsLeftInversion, ht, hconj, false_and, Xor,
      not_false_eq_true, false_or]

/-- A reflection is a left inversion of a product exactly when it belongs to exactly one
of the first inversion set and the conjugated second inversion set. -/
theorem leftInversion_mul_iff (cs : CoxeterSystem matrix W) (u v t : W) :
    cs.IsLeftInversion (u * v) t ↔
      Xor (cs.IsLeftInversion u t) (cs.IsLeftInversion v (u⁻¹ * t * u)) :=
  inversion_mul_iff (geometricRealization matrix cs) u v t

end BruhatIntervals
