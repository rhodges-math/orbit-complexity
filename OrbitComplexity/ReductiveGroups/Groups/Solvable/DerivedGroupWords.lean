import Mathlib.GroupTheory.Commutator.Basic

/-!
# Derived Group Words

Balanced derived commutator words, with one index for each leaf. -/

namespace ReductiveGroups
open scoped commutatorElement

/-- Leaves of a balanced derived word. There are `2^n` leaves at depth `n`. -/
def DerivedWordIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => Bool × DerivedWordIndex n

/-- The balanced derived commutator word, with the group commutator convention
`⁅a,b⁆ = a*b*a⁻¹*b⁻¹`. -/
def derivedGroupWord {G : Type*} [Group G] :
    (n : ℕ) → (DerivedWordIndex n → G) → G
  | 0, x => x PUnit.unit
  | n + 1, x =>
      ⁅derivedGroupWord n (fun i => x (false, i)),
        derivedGroupWord n (fun i => x (true, i))⁆

/-- The equality is

```lean
derivedGroupWord 0 x = x PUnit.unit
```
-/
@[simp] theorem derivedGroupWord_zero {G : Type*} [Group G]
    (x : DerivedWordIndex 0 → G) :
    derivedGroupWord 0 x = x PUnit.unit := rfl

/-- The equality is

```lean
derivedGroupWord (n + 1) x =
      ⁅derivedGroupWord n (fun i => x (false, i)),
        derivedGroupWord n (fun i => x (true, i))⁆
```
-/
@[simp] theorem derivedGroupWord_succ {G : Type*} [Group G]
    (n : ℕ) (x : DerivedWordIndex (n + 1) → G) :
    derivedGroupWord (n + 1) x =
      ⁅derivedGroupWord n (fun i => x (false, i)),
        derivedGroupWord n (fun i => x (true, i))⁆ := rfl

/-- The equality is

```lean
f (derivedGroupWord n x) = derivedGroupWord n (fun i => f (x i))
```
-/
theorem derivedGroupWord_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (n : ℕ) (x : DerivedWordIndex n → G) :
    f (derivedGroupWord n x) = derivedGroupWord n (fun i => f (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [derivedGroupWord_succ, map_commutatorElement, ih]

end ReductiveGroups
