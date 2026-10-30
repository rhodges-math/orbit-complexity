import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionsWords
import Mathlib.Data.Set.Card

/-!
# Minimal lengths of distinct simple words from inversion counts

All counts are cardinalities of the positive-to-negative inversion sets.
We first derive deletion for a negative simple-root image, then bound inversion
count by the length of an arbitrary simple word. Distinct simple words attain
that bound, so they have minimal length among every expression in these
simple reflections.

Mathlib's `CoxeterSystem.IsReduced` requires an already constructed Coxeter
system. The final theorem here compares all word lengths directly;
the Coxeter system on the root-theoretic Weyl group is constructed in
`Roots/PresentationWordPropertyCoxeter.lean`.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι]

/-- Inversion sets are finite because they are images of root indices. -/
theorem leftRootInversions_finite (b : P.Base) (w : P.weylGroup) :
    (leftRootInversions b w).Finite :=
  (Set.toFinite (leftRootInversionIndices b w)).image P.root

/-- The number of positive roots sent negative by the inverse action. -/
def rootInversionCount (b : P.Base) (w : P.weylGroup) : ℕ :=
  (leftRootInversions b w).ncard

omit [Finite ι] in
/-- The equality is

```lean
rootInversionCount b 1 = 0
```
-/
@[simp]
theorem rootInversionCount_one (b : P.Base) : rootInversionCount b 1 = 0 := by
  simp [rootInversionCount]

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- Reversing the insertion update when the next image is negative. -/
theorem LeftRootInversions.eq_insert_mul_simple_of_neg (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.height (P.weylGroupToPerm w i) < 0) :
    leftRootInversions b w = insert (-(w • P.root i))
      (leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i)) := by
  have hpos : b.IsPos (P.weylGroupToPerm (w * RootPairing.weylGroup.ofIdx P i) i) := by
    rw [map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple,
      weylGroupToPerm_neg_index, isPos_neg_index_iff]
    exact (root_height_neg_iff_not_isPos b _).mp hw
  have hss : RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P i = 1 := by
    calc
      RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P i =
          RootPairing.weylGroup.ofIdx P i * (RootPairing.weylGroup.ofIdx P i)⁻¹ := by
            rw [weylGroup_simple_inv]
      _ = 1 := mul_inv_cancel _
  have hcancel : (w * RootPairing.weylGroup.ofIdx P i) * RootPairing.weylGroup.ofIdx P i = w := by
    rw [mul_assoc, hss, mul_one]
  have hroot : (w * RootPairing.weylGroup.ofIdx P i) • P.root i = -(w • P.root i) := by
    simp only [mul_smul, RootPairing.weylGroup.ofIdx_smul,
      RootPairing.Equiv.reflection_smul, P.reflection_apply_self, smul_neg]
  simpa only [hcancel, hroot] using
    leftRootInversions_mul_simple b (w * RootPairing.weylGroup.ofIdx P i) i hpos

/-- A negative simple-root image deletes its opposite from the inversion set. -/
theorem leftRootInversions_mul_simple_of_neg (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.height (P.weylGroupToPerm w i) < 0) :
    leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) =
      leftRootInversions b w \ {-(w • P.root i)} := by
  have hnot : -(w • P.root i) ∉
      leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) := by
    simpa only [mul_smul, RootPairing.weylGroup.ofIdx_smul,
      RootPairing.Equiv.reflection_smul, P.reflection_apply_self, smul_neg] using
      simple_image_notMem_leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) i
  rw [LeftRootInversions.eq_insert_mul_simple_of_neg b w i hw,
    Set.insert_sdiff_self_of_notMem hnot]

/-- The positive-image insertion increases the inversion count by one. -/
theorem rootInversionCount_mul_simple_of_pos (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.IsPos (P.weylGroupToPerm w i)) :
    rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) = rootInversionCount b w + 1 := by
  unfold rootInversionCount
  rw [leftRootInversions_mul_simple b w i hw]
  exact Set.ncard_insert_of_notMem (simple_image_notMem_leftRootInversions b w i)
    (leftRootInversions_finite b w)

/-- The negative-image deletion decreases the inversion count by one.
The additive form also records that the original count was positive. -/
theorem rootInversionCount_mul_simple_of_neg (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.height (P.weylGroupToPerm w i) < 0) :
    rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) + 1 = rootInversionCount b w := by
  have hnot : -(w • P.root i) ∉
      leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) := by
    simpa only [mul_smul, RootPairing.weylGroup.ofIdx_smul,
      RootPairing.Equiv.reflection_smul, P.reflection_apply_self, smul_neg] using
      simple_image_notMem_leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) i
  unfold rootInversionCount
  rw [LeftRootInversions.eq_insert_mul_simple_of_neg b w i hw,
    Set.ncard_insert_of_notMem hnot
      (leftRootInversions_finite b (w * RootPairing.weylGroup.ofIdx P i))]

/-- An arbitrary appended simple reflection increases the inversion count by at most one. -/
theorem rootInversionCount_mul_simple_le (b : P.Base) (w : P.weylGroup) (i : b.support) :
    rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) ≤ rootInversionCount b w + 1 := by
  by_cases hw : b.IsPos (P.weylGroupToPerm w i)
  · exact (rootInversionCount_mul_simple_of_pos b w i hw).le
  · have hneg := rootInversionCount_mul_simple_of_neg b w i
      ((root_height_neg_iff_not_isPos b _).mpr hw)
    omega

/-- The inversion count is bounded by the length of every simple-word expression. -/
theorem RootInversionCount.simpleWeylWord_le_length (b : P.Base) (l : List b.support) :
    rootInversionCount b (simpleWeylWord b l) ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [simpleWeylWord]
  | append_singleton l i ih =>
    rw [simpleWeylWord_append]
    simp only [simpleWeylWord, mul_one, List.length_append, List.length_singleton]
    exact (rootInversionCount_mul_simple_le b (simpleWeylWord b l) i).trans
      (Nat.add_le_add_right ih 1)

variable [P.IsRootSystem]

/-- A distinct simple word attains the inversion-count bound, by disjoint insertion. -/
theorem RootInversionCount.simpleWeylWord_eq_length (b : P.Base) (l : List b.support) :
    l.Nodup → rootInversionCount b (simpleWeylWord b l) = l.length := by
  induction l using List.reverseRecOn with
  | nil => intro _; simp [simpleWeylWord]
  | append_singleton l i ih =>
    intro hnodup
    obtain ⟨hl, _, hdisjoint⟩ := List.nodup_append.mp hnodup
    have hi : i ∉ l := fun h => hdisjoint i h i (by simp) rfl
    rw [simpleWeylWord_append]
    simp only [simpleWeylWord, mul_one, List.length_append, List.length_singleton]
    rw [rootInversionCount_mul_simple_of_pos b (simpleWeylWord b l) i
      (simpleWeylWord_isPos_of_notMem b l hi), ih hl]

/-- A distinct simple word is minimal against every expression in these
simple reflections. This is reducedness, proved by inversion counts. -/
theorem simpleWeylWord_length_le_of_nodup (b : P.Base) (l m : List b.support)
    (hl : l.Nodup) (hm : simpleWeylWord b m = simpleWeylWord b l) : l.length ≤ m.length := by
  calc
    l.length = rootInversionCount b (simpleWeylWord b l) :=
      (RootInversionCount.simpleWeylWord_eq_length b l hl).symm
    _ = rootInversionCount b (simpleWeylWord b m) := congrArg (rootInversionCount b) hm.symm
    _ ≤ m.length := RootInversionCount.simpleWeylWord_le_length b m

end ReductiveGroups
