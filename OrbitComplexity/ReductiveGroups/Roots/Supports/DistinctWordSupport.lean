import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSupportStability
import OrbitComplexity.ReductiveGroups.Roots.Inversions.AmbientInversions

/-!
# Distinct Word Support

Exact simple-coordinate support control for a word acting on a
simple root. These lemmas justify that each effective reflection in the
paper's distinct-letter growth argument acts at an omitted simple root. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]

omit [P.IsCrystallographic] in
/-- The equality is

```lean
simpleRootSupportInt b (i : ι) = {i}
```
-/
theorem simpleRootSupportInt_simple_eq (b : P.Base) (i : b.support) :
    simpleRootSupportInt b (i : ι) = {i} := by
  ext j
  change (simpleRootCoeffInt b (i : ι) j ≠ 0) ↔ j = i
  rw [simpleRootCoeffInt_simple]
  by_cases hij : i = j <;> simp [hij, eq_comm]

/-- Only the initial simple root and the reflected simple vertices can
occur in the support. The word need not be reduced. -/
theorem simpleWeylWord_simple_support_subset (b : P.Base)
    (word : List b.support) (i : b.support) :
    simpleRootSupportInt b (P.weylGroupToPerm (simpleWeylWord b word) (i : ι)) ⊆
      insert i {j | j ∈ word} := by
  apply simpleWeylWord_preserves_root_support b (insert i {j | j ∈ word}) word
  · intro j hj
    exact Or.inr hj
  · rw [simpleRootSupportInt_simple_eq]
    exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

/-- The equality is

```lean
simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) (i : ι)) j = 0
```
-/
theorem SimpleWeylWord.simple_coeff_zero_of_omitted (b : P.Base)
    (word : List b.support) (i j : b.support)
    (hji : j ≠ i) (hj : j ∉ word) :
    simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) (i : ι)) j = 0 := by
  by_contra h
  have hm := simpleWeylWord_simple_support_subset b word i h
  exact hm.elim hji hj

/-- A word omitting a simple vertex leaves that coordinate of every
root unchanged. This is an equality in the integral root basis. -/
theorem SimpleWeylWord.preserves_omitted_coefficient (b : P.Base)
    (word : List b.support) (β : ι) (i : b.support) (hi : i ∉ word) :
    simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) β) i =
      simpleRootCoeffInt b β i := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    have hij : i ≠ j := fun he => hi (by simp [he])
    have hiw : i ∉ word := fun h => hi (List.mem_cons_of_mem _ h)
    change simpleRootCoeffInt b
      (P.reflectionPerm (j : ι) (P.weylGroupToPerm (simpleWeylWord b word) β)) i = _
    rw [simpleRootCoeffInt_reflection, ite_eq_right hij.symm, mul_zero, sub_zero]
    exact ih hiw

/-- The equality is

```lean
simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) (i : ι)) i = 1
```
-/
theorem simpleWeylWord_initial_coeff_one (b : P.Base)
    (word : List b.support) (i : b.support) (hi : i ∉ word) :
    simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) (i : ι)) i = 1 := by
  rw [SimpleWeylWord.preserves_omitted_coefficient b word (i : ι) i hi,
    simpleRootCoeffInt_simple, ite_eq_left rfl]

end ReductiveGroups
