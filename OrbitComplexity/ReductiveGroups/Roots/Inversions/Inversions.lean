import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# Left inversions from root signs

The left inversion set consists of roots characterized by positivity of a root and negativity of its
image under `w⁻¹`. We use precisely those signs, with Mathlib's base height and
the Weyl-group action. No inversion set is defined from a word.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The indices of positive roots sent to negative roots by `w⁻¹`. -/
def leftRootInversionIndices (b : P.Base) (w : P.weylGroup) : Set ι :=
  {i | b.IsPos i ∧ b.height (P.weylGroupToPerm w⁻¹ i) < 0}

/-- the left inversion set, as ordinary sets of root vectors. -/
def leftRootInversions (b : P.Base) (w : P.weylGroup) : Set M :=
  P.root '' leftRootInversionIndices b w

/-- The equivalence is

```lean
b.height i < 0 ↔ ¬ b.IsPos i
```
-/
theorem root_height_neg_iff_not_isPos (b : P.Base) (i : ι) :
    b.height i < 0 ↔ ¬ b.IsPos i := by
  rw [b.isPos_iff', not_le]

/-- The equivalence is

```lean
i ∈ leftRootInversionIndices b w ↔
      b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w⁻¹ i)
```
-/
@[simp]
theorem mem_leftRootInversionIndices (b : P.Base) (w : P.weylGroup) (i : ι) :
    i ∈ leftRootInversionIndices b w ↔
      b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w⁻¹ i) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [root_height_neg_iff_not_isPos]

/-- The equivalence is

```lean
P.root i ∈ leftRootInversions b w ↔ i ∈ leftRootInversionIndices b w
```
-/
@[simp]
theorem root_mem_leftRootInversions (b : P.Base) (w : P.weylGroup) (i : ι) :
    P.root i ∈ leftRootInversions b w ↔ i ∈ leftRootInversionIndices b w :=
  P.root.injective.mem_set_image

/-- This vector version exposes the definition through the action on roots. -/
theorem mem_leftRootInversions_iff (b : P.Base) (w : P.weylGroup) (β : M) :
    β ∈ leftRootInversions b w ↔
      ∃ i j : ι, P.root i = β ∧ b.IsPos i ∧ b.height j < 0 ∧
        P.root j = w⁻¹ • β := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, P.weylGroupToPerm w⁻¹ i, rfl, hi.1, hi.2,
      (P.weylGroup_apply_root w⁻¹ i).symm⟩
  · rintro ⟨i, j, rfl, hi, hj, heq⟩
    have hji : j = P.weylGroupToPerm w⁻¹ i :=
      P.root.injective (heq.trans (P.weylGroup_apply_root w⁻¹ i))
    exact ⟨i, ⟨hi, hji ▸ hj⟩, rfl⟩

omit [CharZero R] in
/-- The equality is

```lean
P.weylGroupToPerm (RootPairing.weylGroup.ofIdx P i) = P.reflectionPerm i
```
-/
theorem weylGroupToPerm_simple (i : ι) :
    P.weylGroupToPerm (RootPairing.weylGroup.ofIdx P i) = P.reflectionPerm i := rfl

omit [CharZero R] in
/-- The equality is

```lean
(RootPairing.weylGroup.ofIdx P i)⁻¹ = RootPairing.weylGroup.ofIdx P i
```
-/
@[simp]
theorem weylGroup_simple_inv (i : ι) :
    (RootPairing.weylGroup.ofIdx P i)⁻¹ = RootPairing.weylGroup.ofIdx P i := by
  apply Subtype.ext
  exact RootPairing.Equiv.reflection_inv P i

/-- Negating a root is implemented by its own reflection on the root index. -/
theorem isPos_neg_index_iff (b : P.Base) (i : ι) :
    b.IsPos (P.reflectionPerm i i) ↔ ¬ b.IsPos i :=
  RootPairing.Base.IsPos.neg_iff_not b i

omit [CharZero R] in
/-- The Weyl permutation commutes with root negation. -/
theorem weylGroupToPerm_neg_index (w : P.weylGroup) (i : ι) :
    P.weylGroupToPerm w (P.reflectionPerm i i) =
      P.reflectionPerm (P.weylGroupToPerm w i) (P.weylGroupToPerm w i) := by
  apply P.root.injective
  calc
    P.root (P.weylGroupToPerm w (P.reflectionPerm i i)) =
        w • P.root (P.reflectionPerm i i) := (P.weylGroup_apply_root _ _).symm
    _ = -(w • P.root i) := by simp
    _ = -P.root (P.weylGroupToPerm w i) := by rw [P.weylGroup_apply_root]
    _ = P.root (P.reflectionPerm (P.weylGroupToPerm w i) (P.weylGroupToPerm w i)) := by
      simp only [P.root_reflectionPerm, P.reflection_apply_self]

/-- The equality is

```lean
leftRootInversionIndices b 1 = ∅
```
-/
@[simp]
theorem leftRootInversionIndices_one (b : P.Base) : leftRootInversionIndices b 1 = ∅ := by
  ext i
  simp

/-- The equality is

```lean
leftRootInversions b 1 = ∅
```
-/
@[simp]
theorem leftRootInversions_one (b : P.Base) : leftRootInversions b 1 = ∅ := by
  simp [leftRootInversions]

/-- The image of a positive simple root is never already a left inversion.
Thus the new root in the multiplication update is disjoint from the old set. -/
theorem simple_image_notMem_leftRootInversions (b : P.Base) (w : P.weylGroup)
    (i : b.support) : w • P.root i ∉ leftRootInversions b w := by
  rw [P.weylGroup_apply_root, root_mem_leftRootInversions, mem_leftRootInversionIndices]
  simp only [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  exact fun h => h.2 (b.isPos_of_mem_support i.property)

section SimpleReflectionSigns

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection preserves the sign of every root except its own positive
and negative root. This is derived from Mathlib's positive-root reflection lemma. -/
theorem isPos_reflectionPerm_iff (b : P.Base) {i j : ι} (hi : i ∈ b.support)
    (hji : j ≠ i) (hjnegi : j ≠ P.reflectionPerm i i) :
    b.IsPos (P.reflectionPerm i j) ↔ b.IsPos j := by
  constructor
  · intro h
    have hne : P.reflectionPerm i j ≠ i := by
      intro heq
      apply hjnegi
      simpa using congrArg (P.reflectionPerm i) heq
    simpa using h.reflectionPerm hi hne
  · exact fun h => h.reflectionPerm hi hji

/-- The unique positive root reversed by a simple reflection is its simple root. -/
theorem leftRootInversionIndices_simple (b : P.Base) (i : b.support) :
    leftRootInversionIndices b (RootPairing.weylGroup.ofIdx P i) = {(i : ι)} := by
  ext j
  simp only [mem_leftRootInversionIndices, weylGroup_simple_inv, weylGroupToPerm_simple,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj, hneg⟩
    by_contra hji
    exact hneg (hj.reflectionPerm i.property hji)
  · rintro rfl
    exact ⟨b.isPos_of_mem_support i.property,
      fun h => (isPos_neg_index_iff b i).mp h (b.isPos_of_mem_support i.property)⟩

/-- The equality is

```lean
leftRootInversions b (RootPairing.weylGroup.ofIdx P i) = {P.root i}
```
-/
theorem leftRootInversions_simple (b : P.Base) (i : b.support) :
    leftRootInversions b (RootPairing.weylGroup.ofIdx P i) = {P.root i} := by
  simp [leftRootInversions, leftRootInversionIndices_simple]

/-- Appending a simple reflection adds its positive image to the left inversions.
The hypothesis is a root-sign condition on the Weyl action. -/
theorem leftRootInversionIndices_mul_simple (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.IsPos (P.weylGroupToPerm w i)) :
    leftRootInversionIndices b (w * RootPairing.weylGroup.ofIdx P i) =
      insert (P.weylGroupToPerm w i) (leftRootInversionIndices b w) := by
  ext j
  by_cases hj : b.IsPos j
  · by_cases hji : j = P.weylGroupToPerm w i
    · subst j
      simp only [Set.mem_insert_iff, true_or, iff_true]
      rw [mem_leftRootInversionIndices]
      refine ⟨hw, ?_⟩
      simp only [mul_inv_rev, weylGroup_simple_inv, map_mul, weylGroupToPerm_simple,
        Equiv.Perm.mul_apply, map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
      exact fun h => (isPos_neg_index_iff b i).mp h (b.isPos_of_mem_support i.property)
    · have hpre : P.weylGroupToPerm w⁻¹ j ≠ (i : ι) := by
        intro h
        apply hji
        simpa [map_inv] using congrArg (P.weylGroupToPerm w) h
      have hnpre : P.weylGroupToPerm w⁻¹ j ≠ P.reflectionPerm i i := by
        intro h
        have heq : j = P.weylGroupToPerm w (P.reflectionPerm i i) := by
          simpa [map_inv] using congrArg (P.weylGroupToPerm w) h
        have hposNeg : b.IsPos
            (P.reflectionPerm (P.weylGroupToPerm w i) (P.weylGroupToPerm w i)) := by
          rw [← weylGroupToPerm_neg_index, ← heq]
          exact hj
        exact ((isPos_neg_index_iff b _).mp hposNeg) hw
      simp only [mem_leftRootInversionIndices, mul_inv_rev, weylGroup_simple_inv,
        map_mul, weylGroupToPerm_simple, Equiv.Perm.mul_apply]
      rw [isPos_reflectionPerm_iff b i.property hpre hnpre]
      simp only [Set.mem_insert_iff, hji, false_or, mem_leftRootInversionIndices]
  · have hji : j ≠ P.weylGroupToPerm w i := by
      intro h
      subst j
      exact hj hw
    simp only [mem_leftRootInversionIndices, hj, false_and, Set.mem_insert_iff,
      or_false, hji]

/-- The same update as an equality of ordinary sets of root vectors. -/
theorem leftRootInversions_mul_simple (b : P.Base) (w : P.weylGroup)
    (i : b.support) (hw : b.IsPos (P.weylGroupToPerm w i)) :
    leftRootInversions b (w * RootPairing.weylGroup.ofIdx P i) =
      insert (w • P.root i) (leftRootInversions b w) := by
  change P.root '' leftRootInversionIndices b (w * RootPairing.weylGroup.ofIdx P i) =
    insert (w • P.root i) (P.root '' leftRootInversionIndices b w)
  rw [leftRootInversionIndices_mul_simple b w i hw, Set.image_insert_eq,
    P.weylGroup_apply_root]

end SimpleReflectionSigns

end ReductiveGroups
