import OrbitComplexity.BruhatIntervals.Order.Interval
import Mathlib.Data.Set.Card

/-!
# Rank sizes of Bruhat intervals

A rank size counts interval vertices at a fixed Coxeter-length difference from the lower
endpoint. Every such set is finite because the interval is finite.

## Main definitions

* `rankSize`: the number of vertices at a given interval rank.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.7.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

/-- The rank size is the number of interval vertices at the given length above its bottom. -/
noncomputable def rankSize (u v : W) (k : ℕ) : ℕ :=
  {w | w ∈ bruhatInterval cs u v ∧ cs.length w = cs.length u + k}.ncard

/-- Ranks above the upper endpoint's length are empty. -/
theorem rankSize_eq_zero_of_lt (u v : W) (k : ℕ)
    (hlt : cs.length v < cs.length u + k) : rankSize cs u v k = 0 := by
  unfold rankSize
  have hempty : {w | w ∈ bruhatInterval cs u v ∧
      cs.length w = cs.length u + k} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hw, hlength⟩
    have hle := hw.2.length_le
    omega
  rw [hempty, Set.ncard_empty]

end BruhatIntervals
