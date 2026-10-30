import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordLength

/-!
# Generation of the Weyl group by base-simple reflections

Mathlib defines the Weyl group using all root reflections. Its root-base
reflection induction proves here that each of those generators is a word
in the base-simple reflections. Consequently `simpleWeylWord` is
surjective. This discharges generation in the Coxeter-presentation bridge;
it does not assert that the Coxeter relations give a complete presentation.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The equality is

```lean
RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P i = 1
```
-/
@[simp] theorem weylGroup_ofIdx_mul_self (i : ι) :
    RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P i = 1 := by
  simpa only [weylGroup_simple_inv] using inv_mul_cancel (RootPairing.weylGroup.ofIdx P i)

/-- Root reflection induction lifts to conjugation in the Weyl group. -/
theorem weylGroup_ofIdx_reflectionPerm (i j : ι) :
    RootPairing.weylGroup.ofIdx P (P.reflectionPerm j i) =
      RootPairing.weylGroup.ofIdx P j * RootPairing.weylGroup.ofIdx P i *
        RootPairing.weylGroup.ofIdx P j := by
  apply Subtype.ext
  change RootPairing.Equiv.reflection P (P.reflectionPerm j i) =
    RootPairing.Equiv.reflection P j * RootPairing.Equiv.reflection P i *
      RootPairing.Equiv.reflection P j
  apply RootPairing.Equiv.weightHom_injective P
  simpa only [map_mul, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.reflection_weightEquiv] using
      P.reflection_reflectionPerm (i := i) (j := j)

/-- The equality is

```lean
RootPairing.weylGroup.ofIdx P (P.reflectionPerm i i) =
      RootPairing.weylGroup.ofIdx P i
```
-/
@[simp] theorem weylGroup_ofIdx_neg_index (i : ι) :
    RootPairing.weylGroup.ofIdx P (P.reflectionPerm i i) =
      RootPairing.weylGroup.ofIdx P i := by
  rw [weylGroup_ofIdx_reflectionPerm, weylGroup_ofIdx_mul_self, one_mul]

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- Every root reflection has an expression in the chosen base-simple reflections. -/
theorem exists_simpleWeylWord_ofIdx (b : P.Base) (i : ι) :
    ∃ l : List b.support, simpleWeylWord b l = RootPairing.weylGroup.ofIdx P i := by
  apply b.induction_reflect i
  · intro j hj
    simpa only [weylGroup_ofIdx_neg_index] using hj
  · intro j hj
    exact ⟨[⟨j, hj⟩], by simp [simpleWeylWord]⟩
  · intro j k hj hk
    obtain ⟨l, hl⟩ := hj
    refine ⟨⟨k, hk⟩ :: (l ++ [⟨k, hk⟩]), ?_⟩
    simp only [simpleWeylWord, simpleWeylWord_append, hl, mul_one,
      weylGroup_ofIdx_reflectionPerm, mul_assoc]

/-- The Weyl group, not a presumed Coxeter presentation, is generated
by these simple words. -/
theorem simpleWeylWord_surjective (b : P.Base) : Function.Surjective (simpleWeylWord b) := by
  rintro ⟨w, hw⟩
  induction hw using RootPairing.weylGroup.induction with
  | mem i => exact exists_simpleWeylWord_ofIdx b i
  | one => exact ⟨[], rfl⟩
  | mul w v hw hv ihw ihv =>
    obtain ⟨l, hl⟩ := ihw
    obtain ⟨m, hm⟩ := ihv
    exact ⟨l ++ m, by rw [simpleWeylWord_append, hl, hm]; rfl⟩

/-- Distinct base-simple indices give distinct Weyl reflections. -/
theorem weylGroup_simple_injective (b : P.Base) :
    Function.Injective (fun i : b.support => RootPairing.weylGroup.ofIdx P i) := by
  intro i j hij
  have hsets := congrArg (leftRootInversionIndices b) hij
  rw [leftRootInversionIndices_simple, leftRootInversionIndices_simple] at hsets
  exact Subtype.ext (Set.singleton_injective hsets)

end ReductiveGroups
