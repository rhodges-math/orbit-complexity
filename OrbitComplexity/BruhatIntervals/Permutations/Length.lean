import OrbitComplexity.BruhatIntervals.Permutations.PositiveRoots
import OrbitComplexity.BruhatIntervals.Realizations.RootSets

/-!
# Permutation length as inversion count

Increasing coordinate pairs parametrize positive roots. A coordinate root is a right inversion
root precisely when the permutation reverses its indices, so its Coxeter length counts the
ordinary inversions of its one-line notation.

## Main results

* `TypeA.root_pair_injective`: increasing coordinate pairs have distinct roots.
* `TypeA.length_eq_inversions`: permutation Coxeter length is the inversion count.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 1.5.
-/

namespace BruhatIntervals.TypeA

/-- Two increasing coordinate pairs give the same root only when both indices agree. -/
theorem root_pair_injective (n : ℕ) {i j k l : Fin (n + 1)} (hij : i < j)
    (heq : root n i j = root n k l) : i = k ∧ j = l := by
  have hfirst : i = k := by
    by_contra hik
    have hvalue := congrFun heq i
    simp only [root, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (ne_of_lt hij), Pi.single_eq_of_ne hik, sub_zero, zero_sub] at hvalue
    by_cases hil : i = l
    · rw [hil, Pi.single_eq_same] at hvalue
      norm_num at hvalue
    · rw [Pi.single_eq_of_ne hil] at hvalue
      norm_num at hvalue
  subst k
  have hlast : j = l := by
    have hvalue := congrFun heq j
    simp only [root, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (ne_of_lt hij).symm, zero_sub, neg_inj] at hvalue
    by_contra hjl
    rw [Pi.single_eq_of_ne hjl] at hvalue
    norm_num at hvalue
  exact ⟨rfl, hlast⟩

/-- The inversion pairs of a permutation have increasing positions and decreasing values. -/
def inversionPairs (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter (fun pair => pair.1 < pair.2 ∧ w pair.2 < w pair.1)

/-- Right inversion roots are exactly the roots of the permutation's inversion pairs. -/
theorem rightInversionRoots_eq (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    (realization n).rightInversionRoots w =
      (fun pair : Fin (n + 1) × Fin (n + 1) => root n pair.1 pair.2) ''
        (inversionPairs n w : Set (Fin (n + 1) × Fin (n + 1))) := by
  ext vector
  rw [(realization n).mem_rightInversionRoots]
  constructor
  · rintro ⟨hpositive, hnegative⟩
    obtain ⟨i, j, hij, rfl⟩ := (Set.ext_iff.mp (positiveRoots_eq n) vector).mp hpositive
    have hreverse : w j < w i := by
      change -coordinateAction n w (root n i j) ∈ (realization n).positiveRoots at hnegative
      rw [coordinateAction_root, ← root_neg n (w j) (w i),
        root_mem_positiveRoots_iff] at hnegative
      exact hnegative
    exact ⟨(i, j), by simpa only [inversionPairs, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] using And.intro hij hreverse, rfl⟩
  · rintro ⟨⟨i, j⟩, hpair, rfl⟩
    obtain ⟨hij, hreverse⟩ : i < j ∧ w j < w i := by
      simpa only [inversionPairs, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] using hpair
    refine ⟨root_mem_positiveRoots n i j hij, ?_⟩
    change -coordinateAction n w (root n i j) ∈ (realization n).positiveRoots
    rw [coordinateAction_root, ← root_neg n (w j) (w i), root_mem_positiveRoots_iff]
    exact hreverse

/-- The Coxeter length of a permutation equals the number of its inversion pairs. -/
theorem length_eq_inversions (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    (coxeterSystem n).length w = (inversionPairs n w).card := by
  rw [← (realization n).rightInversionRoots_ncard, rightInversionRoots_eq]
  have hinjective : Set.InjOn (fun pair : Fin (n + 1) × Fin (n + 1) =>
      root n pair.1 pair.2) (inversionPairs n w : Set (Fin (n + 1) × Fin (n + 1))) := by
    intro pair hpair pair' hpair' heq
    have hlt := (Finset.mem_filter.mp hpair).2.1
    exact Prod.ext (root_pair_injective n hlt heq).1 (root_pair_injective n hlt heq).2
  rw [hinjective.ncard_image, Set.ncard_coe_finset]

end BruhatIntervals.TypeA
