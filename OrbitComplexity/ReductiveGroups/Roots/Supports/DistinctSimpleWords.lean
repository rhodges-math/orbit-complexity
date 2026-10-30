import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.List.Induction

/-!
# Distinct simple words and the triangular coefficient argument

We use Mathlib's `RootPairing.Base` and root reflections. For a word
`[i₁, …, iᵣ]` the set `wordRootSet` consists of
`αᵢ₁, sᵢ₁(αᵢ₂), …, sᵢ₁ ⋯ sᵢᵣ₋₁(αᵢᵣ)`.

The proof follows the first paragraph of item (2) of
: append a new simple reflection, use its
coefficient to separate the new root from the span of all earlier roots, and
conclude independence by induction. Triangularity is proved from the reflection
formula, not included as a hypothesis.

`P.IsRootSystem` means the roots span `M`. Thus `M` here is the root space;
it is not identified with the full character space of an arbitrary reductive
group. The identification of `wordRootSet` with the left inversion set is
`leftRootInversions_simpleWeylWord_eq_wordRootSet_ambient`
(`Roots/AmbientInversions.lean`); the comparison with the roots of a reductive
group is in `Groups/BorelRootSystemBridge.lean`.
-/

noncomputable section

namespace ReductiveGroups

open Module

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The ordered product of the reflections attached to a simple word.
Multiplication acts on a vector from right to left. -/
def simpleReflectionWord (b : P.Base) : List b.support → M ≃ₗ[R] M
  | [] => 1
  | i :: l => P.reflection i * simpleReflectionWord b l

/-- Prefix-transformed simple roots of a word. This definition does not assume
that the word is reduced or that these roots form its Coxeter inversion set. -/
def wordRootSet (b : P.Base) : List b.support → Set M
  | [] => ∅
  | i :: l => insert (P.root i) ((P.reflection i) '' wordRootSet b l)

/-- The equality is

```lean
simpleReflectionWord b (l ++ m) = simpleReflectionWord b l * simpleReflectionWord b m
```
-/
theorem simpleReflectionWord_append (b : P.Base) (l m : List b.support) :
    simpleReflectionWord b (l ++ m) = simpleReflectionWord b l * simpleReflectionWord b m := by
  induction l with
  | nil => simp [simpleReflectionWord]
  | cons i l ih => simp [simpleReflectionWord, ih, mul_assoc]

/-- Concatenating words concatenates their prefix roots after transforming the
roots of the second word by the first word. -/
theorem wordRootSet_append (b : P.Base) (l m : List b.support) :
    wordRootSet b (l ++ m) =
      wordRootSet b l ∪ simpleReflectionWord b l '' wordRootSet b m := by
  induction l with
  | nil => simp [wordRootSet, simpleReflectionWord]
  | cons i l ih =>
    simp only [List.cons_append, wordRootSet, simpleReflectionWord, ih, Set.image_union,
      Set.image_image, Set.insert_union]
    rfl

/-- The new last root is the prefix word applied to the appended simple root. -/
theorem wordRootSet_append_singleton (b : P.Base) (l : List b.support) (i : b.support) :
    wordRootSet b (l ++ [i]) =
      insert (simpleReflectionWord b l (P.root i)) (wordRootSet b l) := by
  rw [wordRootSet_append]
  simp [wordRootSet, Set.union_singleton]

/-- Every prefix-transformed simple root is a root of `P`. -/
theorem wordRootSet_subset_range_root (b : P.Base) (l : List b.support) :
    wordRootSet b l ⊆ Set.range P.root := by
  induction l with
  | nil => exact Set.empty_subset _
  | cons i l ih =>
    rintro β (rfl | ⟨γ, hγ, rfl⟩)
    · exact Set.mem_range_self (i : ι)
    · exact P.mapsTo_reflection_root i (ih hγ)

section Coordinates

variable [P.IsRootSystem]

/-- A simple-root coefficient in Mathlib's root-space basis. -/
def simpleRootCoeff (b : P.Base) (i : b.support) : M →ₗ[R] R :=
  b.toWeightBasis.coord i

/-- The equality is

```lean
simpleRootCoeff b i (P.root i) = 1
```
-/
@[simp]
theorem simpleRootCoeff_root_self (b : P.Base) (i : b.support) :
    simpleRootCoeff b i (P.root i) = 1 := by
  simp [simpleRootCoeff, Basis.coord_apply]

/-- The equality is

```lean
simpleRootCoeff b i (P.root j) = 0
```
-/
theorem simpleRootCoeff_root_of_ne (b : P.Base) {i j : b.support} (hij : i ≠ j) :
    simpleRootCoeff b i (P.root j) = 0 := by
  classical
  simp [simpleRootCoeff, Basis.coord_apply, hij]

/-- Reflection in a different simple root preserves the chosen coefficient. -/
theorem simpleRootCoeff_reflection_of_ne (b : P.Base) {i j : b.support}
    (hij : i ≠ j) (x : M) :
    simpleRootCoeff b i (P.reflection j x) = simpleRootCoeff b i x := by
  rw [P.reflection_apply, map_sub, map_smul, simpleRootCoeff_root_of_ne b hij,
    smul_zero, sub_zero]

/-- A word omitting a simple root preserves its coefficient on every vector. -/
theorem simpleRootCoeff_word_of_notMem (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) (x : M) :
    simpleRootCoeff b i (simpleReflectionWord b l x) = simpleRootCoeff b i x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    change simpleRootCoeff b i (P.reflection j (simpleReflectionWord b l x)) = _
    rw [simpleRootCoeff_reflection_of_ne b hij, ih hil]

/-- Earlier prefix roots have coefficient zero at every omitted simple root. -/
theorem simpleRootCoeff_wordRootSet_eq_zero (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) {β : M} (hβ : β ∈ wordRootSet b l) :
    simpleRootCoeff b i β = 0 := by
  induction l generalizing β with
  | nil => exact False.elim hβ
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    rcases hβ with rfl | ⟨γ, hγ, rfl⟩
    · exact simpleRootCoeff_root_of_ne b hij
    · rw [simpleRootCoeff_reflection_of_ne b hij]
      exact ih hil hγ

/-- The new last root has coefficient one on the new simple root. -/
theorem simpleRootCoeff_new_word_root (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) :
    simpleRootCoeff b i (simpleReflectionWord b l (P.root i)) = 1 := by
  rw [simpleRootCoeff_word_of_notMem b l hi, simpleRootCoeff_root_self]

/-- The omitted-simple-root coefficient vanishes on the entire earlier span. -/
theorem simpleRootCoeff_span_wordRootSet_eq_zero (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) {β : M}
    (hβ : β ∈ Submodule.span R (wordRootSet b l)) : simpleRootCoeff b i β = 0 := by
  have hspan : Submodule.span R (wordRootSet b l) ≤
      LinearMap.ker (simpleRootCoeff b i) :=
    Submodule.span_le.mpr fun _ hγ => simpleRootCoeff_wordRootSet_eq_zero b l hi hγ
  exact hspan hβ

/-- The coefficient argument separates the new root from the earlier span. -/
theorem new_word_root_notMem_span [Nontrivial R] (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) :
    simpleReflectionWord b l (P.root i) ∉ Submodule.span R (wordRootSet b l) := by
  intro h
  have hzero := simpleRootCoeff_span_wordRootSet_eq_zero b l hi h
  rw [simpleRootCoeff_new_word_root b l hi] at hzero
  exact one_ne_zero hzero

/-- The prefix roots of a word in pairwise distinct simple reflections are
linearly independent. The last-letter induction uses the coefficient-one and
coefficient-zero statements proved above. -/
theorem wordRootSet_linearIndepOn (b : P.Base) (l : List b.support) :
    l.Nodup → LinearIndepOn R id (wordRootSet b l) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    exact linearIndepOn_empty R id
  | append_singleton l i ih =>
    intro hnodup
    obtain ⟨hl, _, hdisjoint⟩ := List.nodup_append.mp hnodup
    have hi : i ∉ l := fun h => hdisjoint i h i (by simp) rfl
    rw [wordRootSet_append_singleton]
    apply (ih hl).id_insert'
    intro r hr
    have hzero := simpleRootCoeff_span_wordRootSet_eq_zero b l hi hr
    simpa only [map_smul, simpleRootCoeff_new_word_root b l hi, smul_eq_mul, mul_one] using hzero

end Coordinates

end ReductiveGroups
