import OrbitComplexity.ReductiveGroups.Roots.Supports.DistinctSimpleWords

/-!
# Triangular simple-root coordinates on the root span

The base gives a basis of `P.rootSpan R`, even when roots do not span the
ambient module. Reflections restrict to this submodule. the coefficient-zero/coefficient-one
argument is carried out on it and proves
independence of the existing, ambient `wordRootSet`.
-/

noncomputable section

namespace ReductiveGroups

open Module

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The simple roots are a basis of their root submodule. -/
def rootSpanBasis (b : P.Base) : Basis b.support R (P.rootSpan R) :=
  (Basis.span b.linearIndepOn_root).map
    (LinearEquiv.ofEq _ _ (by simpa only [Set.image_eq_range] using b.span_root_support))

/-- The equality is

```lean
rootSpanBasis b i = P.rootSpanMem R i
```
-/
@[simp]
theorem rootSpanBasis_apply (b : P.Base) (i : b.support) :
    rootSpanBasis b i = P.rootSpanMem R i := by
  apply Subtype.ext
  exact Basis.coe_span_apply b.linearIndepOn_root i

/-- Coordinates are defined only on the root submodule, not on all of `M`. -/
def rootSpanCoeff (b : P.Base) (i : b.support) : P.rootSpan R →ₗ[R] R :=
  (rootSpanBasis b).coord i

/-- The equality is

```lean
rootSpanCoeff b i (P.rootSpanMem R i) = 1
```
-/
@[simp]
theorem rootSpanCoeff_root_self (b : P.Base) (i : b.support) :
    rootSpanCoeff b i (P.rootSpanMem R i) = 1 := by
  rw [← rootSpanBasis_apply]
  simp only [rootSpanCoeff, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

/-- The equality is

```lean
rootSpanCoeff b i (P.rootSpanMem R j) = 0
```
-/
theorem rootSpanCoeff_root_of_ne (b : P.Base) {i j : b.support} (hij : i ≠ j) :
    rootSpanCoeff b i (P.rootSpanMem R j) = 0 := by
  classical
  rw [← rootSpanBasis_apply]
  simp only [rootSpanCoeff, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_of_ne hij]

/-- The reflection formula itself shows preservation of the root submodule. -/
theorem reflection_mem_rootSpan (i : ι) {x : M} (hx : x ∈ P.rootSpan R) :
    P.reflection i x ∈ P.rootSpan R := by
  rw [P.reflection_apply]
  exact (P.rootSpan R).sub_mem hx ((P.rootSpan R).smul_mem _ (P.rootSpanMem R i).property)

/-- Restriction of the root reflection to the root submodule. -/
def rootSpanReflection (i : ι) : P.rootSpan R ≃ₗ[R] P.rootSpan R where
  toFun x := ⟨P.reflection i x, reflection_mem_rootSpan i x.property⟩
  invFun x := ⟨P.reflection i x, reflection_mem_rootSpan i x.property⟩
  left_inv x := Subtype.ext (P.reflection_same i x)
  right_inv x := Subtype.ext (P.reflection_same i x)
  map_add' x y := Subtype.ext ((P.reflection i).map_add x y)
  map_smul' r x := Subtype.ext ((P.reflection i).map_smul r x)

/-- The equality is

```lean
(rootSpanReflection (P := P) i x : M) = P.reflection i x
```
-/
@[simp]
theorem rootSpanReflection_coe (i : ι) (x : P.rootSpan R) :
    (rootSpanReflection (P := P) i x : M) = P.reflection i x := rfl

/-- The equality is

```lean
rootSpanReflection (P := P) i x = x - (P.coroot' i x) • P.rootSpanMem R i
```
-/
theorem rootSpanReflection_apply (i : ι) (x : P.rootSpan R) :
    rootSpanReflection (P := P) i x = x - (P.coroot' i x) • P.rootSpanMem R i := by
  apply Subtype.ext
  exact P.reflection_apply i x

/-- Restrict the same ordered reflection word; the product convention is unchanged. -/
def rootSpanReflectionWord (b : P.Base) : List b.support → P.rootSpan R ≃ₗ[R] P.rootSpan R
  | [] => 1
  | i :: l => rootSpanReflection (P := P) i * rootSpanReflectionWord b l

/-- The equality is

```lean
(rootSpanReflectionWord b l x : M) = simpleReflectionWord b l x
```
-/
@[simp]
theorem rootSpanReflectionWord_coe (b : P.Base) (l : List b.support) (x : P.rootSpan R) :
    (rootSpanReflectionWord b l x : M) = simpleReflectionWord b l x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change P.reflection i (rootSpanReflectionWord b l x : M) =
      P.reflection i (simpleReflectionWord b l x)
    rw [ih]

/-- Reflection in a different simple root preserves the chosen root-span coefficient. -/
theorem rootSpanCoeff_reflection_of_ne (b : P.Base) {i j : b.support}
    (hij : i ≠ j) (x : P.rootSpan R) :
    rootSpanCoeff b i (rootSpanReflection (P := P) j x) = rootSpanCoeff b i x := by
  rw [rootSpanReflection_apply, map_sub, map_smul, rootSpanCoeff_root_of_ne b hij,
    smul_zero, sub_zero]

/-- The equality is

```lean
rootSpanCoeff b i (rootSpanReflectionWord b l x) = rootSpanCoeff b i x
```
-/
theorem rootSpanCoeff_word_of_notMem (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) (x : P.rootSpan R) :
    rootSpanCoeff b i (rootSpanReflectionWord b l x) = rootSpanCoeff b i x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    change rootSpanCoeff b i (rootSpanReflection (P := P) j (rootSpanReflectionWord b l x)) = _
    rw [rootSpanCoeff_reflection_of_ne b hij, ih hil]

/-- The appended root has coefficient one on the new simple root. -/
theorem rootSpanCoeff_new_word_root (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) :
    rootSpanCoeff b i (rootSpanReflectionWord b l (P.rootSpanMem R i)) = 1 := by
  rw [rootSpanCoeff_word_of_notMem b l hi, rootSpanCoeff_root_self]

/-- For these parameters,

```lean
β ∈ P.rootSpan R
```
-/
theorem wordRootSet_mem_rootSpan (b : P.Base) (l : List b.support) {β : M}
    (hβ : β ∈ wordRootSet b l) : β ∈ P.rootSpan R := by
  obtain ⟨i, rfl⟩ := wordRootSet_subset_range_root b l hβ
  exact (P.rootSpanMem R i).property

/-- The inclusion is

```lean
Submodule.span R (wordRootSet b l) ≤ P.rootSpan R
```
-/
theorem span_wordRootSet_le_rootSpan (b : P.Base) (l : List b.support) :
    Submodule.span R (wordRootSet b l) ≤ P.rootSpan R :=
  Submodule.span_le.mpr (fun _ hβ => wordRootSet_mem_rootSpan b l hβ)

/-- Every earlier prefix root has coefficient zero at an omitted simple root. -/
theorem rootSpanCoeff_wordRootSet_eq_zero (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) {β : M} (hβ : β ∈ wordRootSet b l) :
    rootSpanCoeff b i ⟨β, wordRootSet_mem_rootSpan b l hβ⟩ = 0 := by
  induction l generalizing β with
  | nil => exact False.elim hβ
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    rcases hβ with rfl | ⟨γ, hγ, rfl⟩
    · exact rootSpanCoeff_root_of_ne b hij
    · change rootSpanCoeff b i
        (rootSpanReflection (P := P) j ⟨γ, wordRootSet_mem_rootSpan b l hγ⟩) = 0
      rw [rootSpanCoeff_reflection_of_ne b hij]
      exact ih hil hγ

/-- The coefficient vanishes on the ambient span of all earlier roots; the
argument is evaluated in its proved containing root submodule. -/
theorem rootSpanCoeff_span_wordRootSet_eq_zero (b : P.Base) (l : List b.support)
    {i : b.support} (hi : i ∉ l) {β : M}
    (hβ : β ∈ Submodule.span R (wordRootSet b l)) :
    rootSpanCoeff b i ⟨β, span_wordRootSet_le_rootSpan b l hβ⟩ = 0 := by
  induction hβ using Submodule.span_induction with
  | mem β hβ => exact rootSpanCoeff_wordRootSet_eq_zero b l hi hβ
  | zero => exact map_zero _
  | add β γ hβ hγ ihβ ihγ =>
    change rootSpanCoeff b i
      (⟨β, span_wordRootSet_le_rootSpan b l hβ⟩ +
       ⟨γ, span_wordRootSet_le_rootSpan b l hγ⟩) = 0
    rw [map_add, ihβ, ihγ, zero_add]
  | smul r β hβ ihβ =>
    change rootSpanCoeff b i (r • ⟨β, span_wordRootSet_le_rootSpan b l hβ⟩) = 0
    rw [map_smul, ihβ, smul_zero]

/-- The ambient prefix-root set is linearly independent. -/
theorem wordRootSet_linearIndepOn_ambient (b : P.Base) (l : List b.support) :
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
    have hzero := rootSpanCoeff_span_wordRootSet_eq_zero b l hi hr
    have he : (⟨r • simpleReflectionWord b l (P.root i),
        span_wordRootSet_le_rootSpan b l hr⟩ : P.rootSpan R) =
          r • rootSpanReflectionWord b l (P.rootSpanMem R i) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, rootSpanReflectionWord_coe]
    rw [he, map_smul, rootSpanCoeff_new_word_root b l hi, smul_eq_mul, mul_one] at hzero
    exact hzero

end ReductiveGroups
