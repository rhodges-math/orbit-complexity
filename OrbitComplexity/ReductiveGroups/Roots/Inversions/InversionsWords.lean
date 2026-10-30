import OrbitComplexity.ReductiveGroups.Roots.Inversions.Inversions
import OrbitComplexity.ReductiveGroups.Roots.Supports.DistinctSimpleWords

/-!
# Comparing left inversions with prefix roots

We prove the comparison for words in pairwise distinct simple reflections of
the Mathlib Weyl group. The inversion set is defined in `Inversions`
using positive and negative root signs. The comparison is not an assumption.

An omitted simple-root coordinate proves that the next image is positive.
The simple-reflection inversion update then gives the prefix-root formula by
last-letter induction, .
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The simple word as an element of Mathlib's Weyl group. -/
def simpleWeylWord (b : P.Base) : List b.support → P.weylGroup
  | [] => 1
  | i :: l => RootPairing.weylGroup.ofIdx P i * simpleWeylWord b l

/-- The equality is

```lean
simpleWeylWord b (l ++ m) = simpleWeylWord b l * simpleWeylWord b m
```
-/
theorem simpleWeylWord_append (b : P.Base) (l m : List b.support) :
    simpleWeylWord b (l ++ m) = simpleWeylWord b l * simpleWeylWord b m := by
  induction l with
  | nil => simp [simpleWeylWord]
  | cons i l ih => simp [simpleWeylWord, ih, mul_assoc]

/-- The Weyl word acts by the previously defined product of linear reflections. -/
theorem simpleWeylWord_smul (b : P.Base) (l : List b.support) (x : M) :
    simpleWeylWord b l • x = simpleReflectionWord b l x := by
  induction l with
  | nil => simp [simpleWeylWord, simpleReflectionWord]
  | cons i l ih =>
    simp only [simpleWeylWord, simpleReflectionWord, mul_smul,
      RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
      LinearEquiv.mul_apply, ih]

/-- The root permutation and root-space reflection product agree on every root. -/
theorem simpleWeylWord_root (b : P.Base) (l : List b.support) (i : ι) :
    P.root (P.weylGroupToPerm (simpleWeylWord b l) i) =
      simpleReflectionWord b l (P.root i) :=
  (P.weylGroup_apply_root _ _).symm.trans (simpleWeylWord_smul b l (P.root i))

section RootSigns

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem]

/-- A word omitting a simple root sends that root to a positive root. The
omitted coordinate remains one and rules out the exceptional sign-changing root
at each simple reflection. -/
theorem simpleWeylWord_isPos_of_notMem (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) :
    b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i) := by
  induction l with
  | nil =>
    simpa only [simpleWeylWord, map_one, Equiv.Perm.one_apply] using
      b.isPos_of_mem_support i.property
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    have hne : P.weylGroupToPerm (simpleWeylWord b l) i ≠ (j : ι) := by
      intro heq
      have hcoord := congrArg (fun k : ι => simpleRootCoeff b i (P.root k)) heq
      rw [simpleWeylWord_root, simpleRootCoeff_new_word_root b l hil,
        simpleRootCoeff_root_of_ne b hij] at hcoord
      exact one_ne_zero hcoord
    change b.IsPos (P.weylGroupToPerm
      (RootPairing.weylGroup.ofIdx P j * simpleWeylWord b l) i)
    rw [map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple]
    exact (ih hil).reflectionPerm j.property hne

/-- Positive-to-negative left inversions are exactly the prefix roots
for a word with pairwise distinct simple letters. -/
theorem LeftRootInversions.simpleWeylWord_eq_wordRootSet (b : P.Base) (l : List b.support) :
    l.Nodup → leftRootInversions b (simpleWeylWord b l) = wordRootSet b l := by
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    simp [simpleWeylWord, wordRootSet]
  | append_singleton l i ih =>
    intro hnodup
    obtain ⟨hl, _, hdisjoint⟩ := List.nodup_append.mp hnodup
    have hi : i ∉ l := fun h => hdisjoint i h i (by simp) rfl
    rw [simpleWeylWord_append]
    simp only [simpleWeylWord, mul_one]
    rw [leftRootInversions_mul_simple b (simpleWeylWord b l) i
      (simpleWeylWord_isPos_of_notMem b l hi), ih hl, wordRootSet_append_singleton,
      simpleWeylWord_smul]

/-- The independent-prefix-root theorem applied to inversion sets. -/
theorem LeftRootInversions.simpleWeylWord_linearIndepOn (b : P.Base) (l : List b.support)
    (hl : l.Nodup) : LinearIndepOn R id (leftRootInversions b (simpleWeylWord b l)) := by
  rw [LeftRootInversions.simpleWeylWord_eq_wordRootSet b l hl]
  exact wordRootSet_linearIndepOn b l hl

/-- Any Weyl element represented by a distinct simple word has a linearly
independent left inversion set. A reduced boolean expression supplies this witness. -/
theorem LeftRootInversions.linearIndepOn_of_distinct_simple_word (b : P.Base)
    (w : P.weylGroup) (hw : ∃ l : List b.support, l.Nodup ∧ simpleWeylWord b l = w) :
    LinearIndepOn R id (leftRootInversions b w) := by
  obtain ⟨l, hl, rfl⟩ := hw
  exact LeftRootInversions.simpleWeylWord_linearIndepOn b l hl

end RootSigns

end ReductiveGroups
