import OrbitComplexity.BruhatIntervals.Permutations.Realization
import OrbitComplexity.BruhatIntervals.Realizations.Translate

/-!
# Positive coordinate roots

The positive roots of the permutation realization are exactly the coordinate differences
`e_i - e_j` with `i < j`. Coordinate permutations carry these differences to differences at
the image indices. Positivity follows by summing consecutive simple roots.

## Main results

* `TypeA.root_mem_positiveRoots_iff`: positivity is strict increase of the two indices.
* `TypeA.positiveRoots_eq`: every positive root is an increasing coordinate difference.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 4.4.
-/

namespace BruhatIntervals.TypeA

/-- A coordinate root is the difference of its two coordinate unit vectors. -/
def root (n : ℕ) (i j : Fin (n + 1)) : Fin (n + 1) → ℝ := Pi.single i 1 - Pi.single j 1

/-- Coordinate permutation sends a unit vector to the unit vector at its image index. -/
theorem coordinateAction_single (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : coordinateAction n σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  ext k
  rw [coordinateAction_apply]
  by_cases heq : k = σ i
  · subst k
    simp
  · have hpre : σ⁻¹ k ≠ i := by
      intro h
      apply heq
      have hback := congrArg σ h
      simpa using hback
    simp only [Pi.single_eq_of_ne hpre, Pi.single_eq_of_ne heq]

/-- Coordinate permutation sends a root to the root at the image indices. -/
theorem coordinateAction_root (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : coordinateAction n σ (root n i j) = root n (σ i) (σ j) := by
  rw [root, map_sub, coordinateAction_single, coordinateAction_single]
  rfl

/-- Reversing the coordinate indices negates their root. -/
theorem root_neg (n : ℕ) (i j : Fin (n + 1)) : root n i j = -root n j i := by
  simp only [root, neg_sub]

private theorem root_transport (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    ∃ k : Fin n, ∃ σ : Equiv.Perm (Fin (n + 1)), σ k.castSucc = i ∧ σ k.succ = j := by
  have hi : i.val < n := by
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  let k : Fin n := ⟨i.val, hi⟩
  have hki : k.castSucc = i := Fin.ext rfl
  have hfirst : i ≠ k.succ := by
    intro h
    have hval := congrArg Fin.val h
    change i.val = i.val + 1 at hval
    omega
  refine ⟨k, Equiv.swap k.succ j, ?_, Equiv.swap_apply_left _ _⟩
  rw [hki, Equiv.swap_apply_of_ne_of_ne hfirst (ne_of_lt hij)]

private theorem root_mem_roots (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    root n i j ∈ (realization n).roots := by
  obtain ⟨k, σ, hfirst, hlast⟩ := root_transport n i j hij
  refine ⟨σ, k, ?_⟩
  change coordinateAction n σ (root n k.castSucc k.succ) = root n i j
  rw [coordinateAction_root, hfirst, hlast]

private theorem root_mem_cone (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    root n i j ∈ (realization n).positiveCone := by
  induction j using Fin.induction generalizing i with
  | zero =>
    change i.val < 0 at hij
    omega
  | succ j ih =>
    by_cases heq : i = j.castSucc
    · subst i
      exact ((realization n).simpleRoot_mem_positiveRoots j).2
    have hij' : i < j.castSucc := by
      have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
      change i.val < j.val + 1 at hij
      change i.val < j.val
      omega
    have hadd : root n i j.succ = root n i j.castSucc + simpleRoot n j := by
      ext k
      simp only [root, simpleRoot, Pi.sub_apply, Pi.add_apply]
      ring
    rw [hadd]
    exact (realization n).positiveCone_add (ih i hij')
      ((realization n).simpleRoot_mem_positiveRoots j).2

/-- An increasing coordinate difference is a positive root of the permutation realization. -/
theorem root_mem_positiveRoots (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    root n i j ∈ (realization n).positiveRoots :=
  ⟨root_mem_roots n i j hij, root_mem_cone n i j hij⟩

/-- A coordinate root is positive exactly when its first index is smaller than its second. -/
theorem root_mem_positiveRoots_iff (n : ℕ) (i j : Fin (n + 1)) :
    root n i j ∈ (realization n).positiveRoots ↔ i < j := by
  constructor
  · intro hroot
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hij
    · exact False.elim ((realization n).root_ne_zero hroot.1 (by simp only [root, sub_self]))
    · have hnegative : -root n i j ∈ (realization n).positiveRoots := by
        rw [← root_neg n j i]
        exact root_mem_positiveRoots n j i hji
      exact False.elim ((realization n).positiveRoots_ne_neg hroot hnegative)
  · exact root_mem_positiveRoots n i j

/-- The positive roots of the permutation realization are precisely the increasing coordinate
differences. -/
theorem positiveRoots_eq (n : ℕ) : (realization n).positiveRoots =
    {vector | ∃ i j : Fin (n + 1), i < j ∧ root n i j = vector} := by
  ext vector
  constructor
  · intro hvector
    obtain ⟨σ, k, hroot⟩ := hvector.1
    change coordinateAction n σ (root n k.castSucc k.succ) = vector at hroot
    rw [coordinateAction_root] at hroot
    refine ⟨σ k.castSucc, σ k.succ, ?_, hroot⟩
    apply (root_mem_positiveRoots_iff n _ _).mp
    rwa [hroot]
  · rintro ⟨i, j, hij, rfl⟩
    exact root_mem_positiveRoots n i j hij

end BruhatIntervals.TypeA
