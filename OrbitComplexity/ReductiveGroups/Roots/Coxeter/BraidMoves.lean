import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength
import Mathlib.Data.List.Chain

/-!
# Contextual braid moves between simple words

A move replaces a full alternating braid word in a specified prefix and
suffix. Its reflexive transitive closure records a finite sequence of such
replacements; neither relation is defined by equality of products.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- A braid replacement, with the unchanged prefix and suffix
and the two distinct simple letters as witnesses. -/
def WeylBraidMove (b : P.Base) (l k : List b.support) : Prop :=
  ∃ (pre post : List b.support) (i j : b.support), i ≠ j ∧
    l = pre ++ CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j ++ post ∧
    k = pre ++ CoxeterSystem.braidWord (simpleCoxeterMatrix b) j i ++ post

/-- A finite chain of braid replacements, allowing a zero-step chain. -/
abbrev WeylBraidChain (b : P.Base) := Relation.ReflTransGen (WeylBraidMove b)

/-- For these parameters,

```lean
WeylBraidMove b k l
```
-/
theorem WeylBraidMove.symm {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) : WeylBraidMove b k l := by
  obtain ⟨pre, post, i, j, hij, hl, hk⟩ := h
  exact ⟨pre, post, j, i, hij.symm, hk, hl⟩

/-- For these parameters,

```lean
WeylBraidMove b (l ++ tail) (k ++ tail)
```
-/
theorem WeylBraidMove.append_right {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) (tail : List b.support) :
    WeylBraidMove b (l ++ tail) (k ++ tail) := by
  obtain ⟨pre, post, i, j, hij, rfl, rfl⟩ := h
  exact ⟨pre, post ++ tail, i, j, hij, by simp only [List.append_assoc],
    by simp only [List.append_assoc]⟩

/-- The equality is

```lean
l.length = k.length
```
-/
theorem WeylBraidMove.length_eq {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) : l.length = k.length := by
  obtain ⟨pre, post, i, j, _, rfl, rfl⟩ := h
  simp only [List.length_append, CoxeterSystem.length_alternatingWord,
    (simpleCoxeterMatrix b).symmetric i j]

/-- The equality is

```lean
simpleWeylWord b l = simpleWeylWord b k
```
-/
theorem WeylBraidMove.simpleWeylWord_eq {b : P.Base} {l k : List b.support}
    (h : WeylBraidMove b l k) : simpleWeylWord b l = simpleWeylWord b k := by
  obtain ⟨pre, post, i, j, _, rfl, rfl⟩ := h
  simp only [simpleWeylWord_append]
  rw [simpleWeylWord_braidWord_eq b i j]

/-- For these parameters,

```lean
WeylBraidChain b k l
```
-/
theorem WeylBraidChain.symm {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) : WeylBraidChain b k l := by
  induction h with
  | refl => exact .refl
  | tail _ hmove ih => exact (Relation.ReflTransGen.single hmove.symm).trans ih

/-- For these parameters,

```lean
WeylBraidChain b (l ++ tail) (k ++ tail)
```
-/
theorem WeylBraidChain.append_right {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) (tail : List b.support) :
    WeylBraidChain b (l ++ tail) (k ++ tail) := by
  induction h with
  | refl => exact .refl
  | tail _ hmove ih => exact ih.tail (hmove.append_right tail)

/-- The equality is

```lean
l.length = k.length
```
-/
theorem WeylBraidChain.length_eq {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) : l.length = k.length := by
  induction h with
  | refl => rfl
  | tail _ hmove ih => exact ih.trans hmove.length_eq

/-- The equality is

```lean
simpleWeylWord b l = simpleWeylWord b k
```
-/
theorem WeylBraidChain.simpleWeylWord_eq {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) : simpleWeylWord b l = simpleWeylWord b k := by
  induction h with
  | refl => rfl
  | tail _ hmove ih => exact ih.trans hmove.simpleWeylWord_eq

/-- Every chain can be exposed as a nonempty list of words with
the prescribed initial and terminal words. -/
theorem WeylBraidChain.exists_list {b : P.Base} {l k : List b.support}
    (h : WeylBraidChain b l k) :
    ∃ path : List (List b.support),
      List.IsChain (WeylBraidMove b) (l :: path) ∧
      (l :: path).getLast (List.cons_ne_nil _ _) = k :=
  List.exists_isChain_cons_of_relationReflTransGen h

end ReductiveGroups
