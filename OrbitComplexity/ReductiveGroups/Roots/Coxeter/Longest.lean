import OrbitComplexity.ReductiveGroups.Roots.Coxeter.FiniteWeyl
import Mathlib.Data.Fintype.Lattice

/-!
# The longest element of a finite Weyl group

The inversion count attains a maximum on the finite Weyl group. A positive
simple-root image would increase that count, so the maximizing element sends
every positive root to a negative root. Reversing root signs characterizes the
element uniquely and makes its square the identity.

## Main definitions

* `ReductiveGroups.longestWeylElement`: the element of maximum inversion count.

## Main results

* `ReductiveGroups.longestWeylElement_isPos_iff`: reversal of root signs.
* `ReductiveGroups.longestWeylElement_sq`: the longest element is an involution.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The inversion count has a maximum on the finite Weyl group. -/
theorem exists_max_rootInversionCount (b : P.Base) :
    ∃ w : P.weylGroup, ∀ v, rootInversionCount b v ≤ rootInversionCount b w := by
  let := weylGroup_finite b
  exact Finite.exists_max (rootInversionCount b)

/-- A Weyl element maximizing the number of positive roots sent negative by its inverse. -/
def longestWeylElement (b : P.Base) : P.weylGroup :=
  Classical.choose (exists_max_rootInversionCount b)

/-- The inversion count of every Weyl element is at most that of the longest element. -/
theorem rootInversionCount_le_longest (b : P.Base) (w : P.weylGroup) :
    rootInversionCount b w ≤ rootInversionCount b (longestWeylElement b) :=
  Classical.choose_spec (exists_max_rootInversionCount b) w

/-- An element of maximum inversion count sends each simple root to a negative root. -/
private theorem not_isPos_simple_of_max (b : P.Base) (w : P.weylGroup)
    (hw : ∀ v, rootInversionCount b v ≤ rootInversionCount b w)
    (i : b.support) : ¬ b.IsPos (P.weylGroupToPerm w i) := by
  intro hi
  have hinc := rootInversionCount_mul_simple_of_pos b w i hi
  have hle := hw (w * RootPairing.weylGroup.ofIdx P i)
  omega

omit [P.IsReduced] in
/-- Negativity on all simple roots implies negativity on all positive roots. -/
private theorem not_isPos_of_simple_neg (b : P.Base) (w : P.weylGroup)
    (hw : ∀ i ∈ b.support, ¬ b.IsPos (P.weylGroupToPerm w i))
    {i : ι} (hi : b.IsPos i) : ¬ b.IsPos (P.weylGroupToPerm w i) := by
  apply (root_height_neg_iff_not_isPos b _).mp
  apply hi.induction_on_add
  · intro j hj
    exact (root_height_neg_iff_not_isPos b _).mpr (hw j hj)
  · intro j k l hroot hj hk
    have hmap : P.root (P.weylGroupToPerm w l) =
        P.root (P.weylGroupToPerm w j) + P.root (P.weylGroupToPerm w k) := by
      rw [← P.weylGroup_apply_root w l, hroot, smul_add,
        P.weylGroup_apply_root, P.weylGroup_apply_root]
    rw [b.height_add hmap]
    exact add_neg hj ((root_height_neg_iff_not_isPos b _).mpr (hw k hk))

/-- The longest Weyl element sends every positive root to a negative root. -/
theorem longestWeylElement_not_isPos (b : P.Base) {i : ι} (hi : b.IsPos i) :
    ¬ b.IsPos (P.weylGroupToPerm (longestWeylElement b) i) := by
  apply not_isPos_of_simple_neg b (longestWeylElement b) ?_ hi
  intro j hj
  exact not_isPos_simple_of_max b (longestWeylElement b)
    (rootInversionCount_le_longest b) ⟨j, hj⟩

/-- The longest Weyl element reverses the sign of every root. -/
theorem longestWeylElement_isPos_iff (b : P.Base) (i : ι) :
    b.IsPos (P.weylGroupToPerm (longestWeylElement b) i) ↔ ¬ b.IsPos i := by
  constructor
  · intro h hi
    exact longestWeylElement_not_isPos b hi h
  · intro hi
    have hneg := longestWeylElement_not_isPos b ((isPos_neg_index_iff b i).mpr hi)
    rw [weylGroupToPerm_neg_index, isPos_neg_index_iff] at hneg
    exact not_not.mp hneg

/-- A Weyl element preserving the signs of all roots is the identity. -/
private theorem eq_one_of_preserves_isPos (b : P.Base) (w : P.weylGroup)
    (hw : ∀ i, b.IsPos (P.weylGroupToPerm w i) ↔ b.IsPos i) : w = 1 := by
  apply (rootInversionCount_eq_zero_iff b w).mp
  have hempty : leftRootInversionIndices b w = ∅ := by
    ext i
    simp only [mem_leftRootInversionIndices, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hni⟩
    apply hni
    apply (hw (P.weylGroupToPerm w⁻¹ i)).mp
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hi
  simp [rootInversionCount, leftRootInversions, hempty]

/-- The square of the longest Weyl element is the identity. -/
theorem longestWeylElement_sq (b : P.Base) :
    longestWeylElement b * longestWeylElement b = 1 := by
  apply eq_one_of_preserves_isPos b
  intro i
  simp only [map_mul, Equiv.Perm.mul_apply, longestWeylElement_isPos_iff, not_not]

/-- Reversing the signs of all roots characterizes the longest Weyl element. -/
theorem eq_longest_of_reverses_isPos (b : P.Base) (w : P.weylGroup)
    (hw : ∀ i, b.IsPos (P.weylGroupToPerm w i) ↔ ¬ b.IsPos i) :
    w = longestWeylElement b := by
  have hprod : w * longestWeylElement b = 1 := by
    apply eq_one_of_preserves_isPos b
    intro i
    simp only [map_mul, Equiv.Perm.mul_apply, hw, longestWeylElement_isPos_iff, not_not]
  calc
    w = (w * longestWeylElement b) * longestWeylElement b := by
      rw [mul_assoc, longestWeylElement_sq, mul_one]
    _ = longestWeylElement b := by rw [hprod, one_mul]

/-- The longest element is the unique element of maximum inversion count. -/
theorem eq_longest_of_max (b : P.Base) (w : P.weylGroup)
    (hw : ∀ v, rootInversionCount b v ≤ rootInversionCount b w) :
    w = longestWeylElement b := by
  apply eq_longest_of_reverses_isPos b w
  have hneg {i : ι} (hi : b.IsPos i) : ¬ b.IsPos (P.weylGroupToPerm w i) := by
    apply not_isPos_of_simple_neg b w ?_ hi
    intro j hj
    exact not_isPos_simple_of_max b w hw ⟨j, hj⟩
  intro i
  constructor
  · intro hi hpos
    exact hneg hpos hi
  · intro hi
    have hn := hneg ((isPos_neg_index_iff b i).mpr hi)
    rw [weylGroupToPerm_neg_index, isPos_neg_index_iff] at hn
    exact not_not.mp hn

end ReductiveGroups
