import OrbitComplexity.ReductiveGroups.Roots.Inversions.RootSpanCoordinates
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionTransport
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordLength

/-!
# Distinct-word inversions in an arbitrary ambient root-pairing module

The triangular calculation on the root submodule supplies the same
sign, inversion, independence, and natural non-sum conclusions without
`P.IsRootSystem`. All conclusions concern the existing Weyl action
and existing root sets in `M`. -/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The restricted reflection word is the Weyl root action. -/
theorem rootSpanReflectionWord_root (b : P.Base) (l : List b.support) (i : ι) :
    rootSpanReflectionWord b l (P.rootSpanMem R i) =
      P.rootSpanMem R (P.weylGroupToPerm (simpleWeylWord b l) i) := by
  apply Subtype.ext
  rw [rootSpanReflectionWord_coe]
  exact (simpleWeylWord_root b l i).symm

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- The coefficient one at an omitted simple root prevents the exceptional
sign-changing reflection, with coordinates taken only in the root submodule. -/
theorem simpleWeylWord_isPos_of_notMem_ambient (b : P.Base) (l : List b.support)
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
      have hcoord := congrArg (fun k : ι => rootSpanCoeff b i (P.rootSpanMem R k)) heq
      rw [← rootSpanReflectionWord_root, rootSpanCoeff_new_word_root b l hil,
        rootSpanCoeff_root_of_ne b hij] at hcoord
      exact one_ne_zero hcoord
    change b.IsPos (P.weylGroupToPerm
      (RootPairing.weylGroup.ofIdx P j * simpleWeylWord b l) i)
    rw [map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple]
    exact (ih hil).reflectionPerm j.property hne

/-- Left inversions equal the existing prefix-root set for a word
with distinct simple letters, even if the ambient module has additional directions. -/
theorem LeftRootInversions.simpleWeylWord_eq_wordRootSet_ambient
    (b : P.Base) (l : List b.support) :
    l.Nodup → leftRootInversions b (simpleWeylWord b l) = wordRootSet b l := by
  induction l using List.reverseRecOn with
  | nil => intro _; simp [simpleWeylWord, wordRootSet]
  | append_singleton l i ih =>
    intro hnodup
    obtain ⟨hl, _, hdisjoint⟩ := List.nodup_append.mp hnodup
    have hi : i ∉ l := fun h => hdisjoint i h i (by simp) rfl
    rw [simpleWeylWord_append]
    simp only [simpleWeylWord, mul_one]
    rw [leftRootInversions_mul_simple b (simpleWeylWord b l) i
      (simpleWeylWord_isPos_of_notMem_ambient b l hi), ih hl,
      wordRootSet_append_singleton, simpleWeylWord_smul]

/-- For these parameters,

```lean
LinearIndepOn R id (leftRootInversions b (simpleWeylWord b l))
```
-/
theorem LeftRootInversions.simpleWeylWord_linearIndepOn_ambient
    (b : P.Base) (l : List b.support) (hl : l.Nodup) :
    LinearIndepOn R id (leftRootInversions b (simpleWeylWord b l)) := by
  rw [LeftRootInversions.simpleWeylWord_eq_wordRootSet_ambient b l hl]
  exact wordRootSet_linearIndepOn_ambient b l hl

/-- For these parameters,

```lean
LinearIndepOn R id (leftRootInversions b w)
```
-/
theorem LeftRootInversions.of_distinct_simple_word_ambient
    (b : P.Base) (w : P.weylGroup)
    (hw : ∃ l : List b.support, l.Nodup ∧ simpleWeylWord b l = w) :
    LinearIndepOn R id (leftRootInversions b w) := by
  obtain ⟨l, hl, rfl⟩ := hw
  exact LeftRootInversions.simpleWeylWord_linearIndepOn_ambient b l hl

/-- A distinct simple word attains its inversion count without a
root-span-equals-ambient hypothesis. -/
theorem RootInversionCount.simpleWeylWord_eq_length_ambient
    (b : P.Base) (l : List b.support) :
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
      (simpleWeylWord_isPos_of_notMem_ambient b l hi), ih hl]

/-- The inclusion is

```lean
l.length ≤ m.length
```
-/
theorem SimpleWeylWord.length_le_of_nodup_ambient (b : P.Base) (l m : List b.support)
    (hl : l.Nodup) (hm : simpleWeylWord b m = simpleWeylWord b l) : l.length ≤ m.length := by
  calc
    l.length = rootInversionCount b (simpleWeylWord b l) :=
      (RootInversionCount.simpleWeylWord_eq_length_ambient b l hl).symm
    _ = rootInversionCount b (simpleWeylWord b m) := congrArg (rootInversionCount b) hm.symm
    _ ≤ m.length := RootInversionCount.simpleWeylWord_le_length b m

/-- The existing partial-sum cone theorem and root-span independence force
total multiplicity one for a root expressed in distinct-word inversions. -/
theorem AmbientInversions.natCoefficientSum_eq_one_ambient (b : P.Base) (l : List b.support)
    (hl : l.Nodup) (t : Finset (leftRootInversions b (simpleWeylWord b l)))
    (n : leftRootInversions b (simpleWeylWord b l) → ℕ) (i : ι)
    (hsum : ∑ δ ∈ t, n δ • (δ : M) = P.root i) : ∑ δ ∈ t, n δ = 1 := by
  have hi : P.root i ∈ leftRootInversions b (simpleWeylWord b l) := by
    apply (root_mem_inversionClosure_iff b (simpleWeylWord b l) i).mp
    rw [← hsum]
    exact AddSubmonoid.sum_mem _ (fun δ _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure δ.property) _)
  exact NatCoefficientSum.eq_one_of_linearIndepOn
    (LeftRootInversions.simpleWeylWord_linearIndepOn_ambient b l hl) t n hi hsum

/-- For these parameters,

```lean
(∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root
```
-/
theorem inversion_natSum_not_root_ambient (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (t : Finset (leftRootInversions b (simpleWeylWord b l)))
    (n : leftRootInversions b (simpleWeylWord b l) → ℕ)
    (hn : 2 ≤ ∑ δ ∈ t, n δ) : (∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root := by
  rintro ⟨i, hi⟩
  have he := AmbientInversions.natCoefficientSum_eq_one_ambient b l hl t n i hi.symm
  omega

/-- The equality is

```lean
LinearIndepOn R id
      ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l))
```
-/
theorem AmbientInversions.simpleWeylWord_linearIndepOn_ambient (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup) :
    LinearIndepOn R id
      ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) :=
  weyl_image_linearIndepOn a
    (LeftRootInversions.simpleWeylWord_linearIndepOn_ambient b l hl)

/-- The equality is

```lean
∑ δ ∈ t, n δ = 1
```
-/
theorem AmbientInversions.WeylImageInversion.natCoefficientSum_eq_one_ambient (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup)
    (t : Finset ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)))
    (n : ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) → ℕ)
    (i : ι) (hsum : ∑ δ ∈ t, n δ • (δ : M) = P.root i) :
    ∑ δ ∈ t, n δ = 1 := by
  have hi : P.root i ∈
      (fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l) := by
    apply (root_mem_weyl_image_inversionClosure_iff b a (simpleWeylWord b l) i).mp
    rw [← hsum]
    exact AddSubmonoid.sum_mem _ (fun δ _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure δ.property) _)
  exact NatCoefficientSum.eq_one_of_linearIndepOn
    (AmbientInversions.simpleWeylWord_linearIndepOn_ambient b a l hl) t n hi hsum

/-- For these parameters,

```lean
(∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root
```
-/
theorem AmbientInversions.image_inversion_natSum_not_root_ambient (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup)
    (t : Finset ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)))
    (n : ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) → ℕ)
    (hn : 2 ≤ ∑ δ ∈ t, n δ) : (∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root := by
  rintro ⟨i, hi⟩
  have he := AmbientInversions.WeylImageInversion.natCoefficientSum_eq_one_ambient b a l hl t n i
    hi.symm
  omega

end ReductiveGroups
