import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWords
import Mathlib.GroupTheory.Solvable

/-!
# Derived Word Solvability

Solvability of the point group supplies a balanced derived-word
identity of the same depth, with all leaf tuples universally quantified. -/

namespace ReductiveGroups
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- For these parameters,

```lean
derivedGroupWord n x ∈ derivedSeries G n
```
-/
theorem derivedGroupWord_mem_derivedSeries
    (n : ℕ) (x : DerivedWordIndex n → G) :
    derivedGroupWord n x ∈ derivedSeries G n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
      exact Subgroup.commutator_mem_commutator (ih _) (ih _)

/-- The equality is

```lean
derivedGroupWord n x = 1
```
-/
theorem DerivedGroupWord.eq_one_of_derivedSeries_eq_bot
    (n : ℕ) (hn : derivedSeries G n = ⊥) (x : DerivedWordIndex n → G) :
    derivedGroupWord n x = 1 := by
  have h := derivedGroupWord_mem_derivedSeries n x
  rw [hn] at h
  exact h

/-- The equality is

```lean
∃ n : ℕ, ∀ x : DerivedWordIndex n → G, derivedGroupWord n x = 1
```
-/
theorem DerivedWordSolvability.exists_identity_of_isSolvable [Group.IsSolvable G] :
    ∃ n : ℕ, ∀ x : DerivedWordIndex n → G, derivedGroupWord n x = 1 := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact ⟨n, fun x => DerivedGroupWord.eq_one_of_derivedSeries_eq_bot n hn x⟩

end ReductiveGroups
