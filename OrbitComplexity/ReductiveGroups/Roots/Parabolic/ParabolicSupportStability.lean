import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicRootSupport

/-!
# Parabolic Support Stability

The standard parabolic subgroup preserves roots supported on
its prescribed simple vertices. This supplies support control for the
transported auxiliary roots. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [IsDomain R] [Finite ι] [P.IsReduced] in
/-- The equality is

```lean
simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) i =
      simpleRootCoeffInt b β i - P.pairingIn ℤ β (j : ι) *
        (if j = i then 1 else 0)
```
-/
theorem simpleRootCoeffInt_reflection (b : P.Base) (β : ι)
    (j i : b.support) :
    simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) i =
      simpleRootCoeffInt b β i - P.pairingIn ℤ β (j : ι) *
        (if j = i then 1 else 0) := by
  have hspan : P.rootSpanMem ℤ (P.reflectionPerm (j : ι) β) =
      P.rootSpanMem ℤ β -
        P.pairingIn ℤ β (j : ι) • P.rootSpanMem ℤ (j : ι) := by
    apply Subtype.ext
    change P.root (P.reflectionPerm (j : ι) β) =
      P.root β - P.pairingIn ℤ β (j : ι) • P.root (j : ι)
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ]
  have hc := congrArg (fun x : P.rootSpan ℤ => (b.toWeightBasisInt.repr x) i) hspan
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul] at hc
  change simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) i =
    simpleRootCoeffInt b β i - P.pairingIn ℤ β (j : ι) *
      simpleRootCoeffInt b (j : ι) i at hc
  simpa only [simpleRootCoeffInt_simple] using hc

omit [IsDomain R] [Finite ι] [P.IsReduced] in
/-- The inclusion is

```lean
simpleRootSupportInt b (P.reflectionPerm (j : ι) β) ⊆ J
```
-/
theorem simpleRootSupport_reflection_subset (b : P.Base) (J : Set b.support)
    (β : ι) (hβ : simpleRootSupportInt b β ⊆ J)
    (j : b.support) (hj : j ∈ J) :
    simpleRootSupportInt b (P.reflectionPerm (j : ι) β) ⊆ J := by
  intro i hi
  by_contra hiJ
  have hij : j ≠ i := by intro he; exact hiJ (he ▸ hj)
  have hz : simpleRootCoeffInt b β i = 0 := by
    by_contra hne
    exact hiJ (hβ hne)
  apply hi
  rw [simpleRootCoeffInt_reflection, ite_eq_right hij, mul_zero, sub_zero, hz]

omit [IsDomain R] [Finite ι] [P.IsReduced] in
/-- The inclusion is

```lean
simpleRootSupportInt b (P.weylGroupToPerm (simpleWeylWord b word) β) ⊆ J
```
-/
theorem simpleWeylWord_preserves_root_support (b : P.Base) (J : Set b.support)
    (word : List b.support) (hword : ∀ j ∈ word, j ∈ J)
    (β : ι) (hβ : simpleRootSupportInt b β ⊆ J) :
    simpleRootSupportInt b (P.weylGroupToPerm (simpleWeylWord b word) β) ⊆ J := by
  induction word with
  | nil => simpa [simpleWeylWord] using hβ
  | cons j word ih =>
    have htail := ih (fun i hi => hword i (List.mem_cons_of_mem _ hi))
    have hhead := simpleRootSupport_reflection_subset b J
      (P.weylGroupToPerm (simpleWeylWord b word) β) htail j (hword j (by simp))
    exact hhead

/-- The inclusion is

```lean
simpleRootSupportInt b (P.weylGroupToPerm a β) ⊆ J
```
-/
theorem standardParabolic_preserves_root_support (b : P.Base) (J : Set b.support)
    (a : P.weylGroup) (ha : a ∈ standardParabolicSubgroup b J)
    (β : ι) (hβ : simpleRootSupportInt b β ⊆ J) :
    simpleRootSupportInt b (P.weylGroupToPerm a β) ⊆ J := by
  obtain ⟨word, hword, rfl⟩ := (mem_standardParabolicSubgroup_iff_word b J a).mp ha
  exact simpleWeylWord_preserves_root_support b J word hword β hβ

end ReductiveGroups
