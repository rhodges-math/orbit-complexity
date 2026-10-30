import OrbitComplexity.ReductiveGroups.Roots.Coxeter.SimpleGeneration

/-!
# Exchange from a simple-root sign crossing

For an arbitrary simple word whose action sends a chosen simple root
negative, right multiplication by its reflection deletes one letter.
The proof tracks the root through suffixes. At the positive-to-negative
crossing the current root is the simple root of the crossing reflection;
the reflection intertwining identity then cancels that letter.

-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The equality is

```lean
RootPairing.weylGroup.ofIdx P i * (RootPairing.weylGroup.ofIdx P i * w) = w
```
-/
@[simp] theorem weylGroup_ofIdx_mul_cancel_left (i : ι) (w : P.weylGroup) :
    RootPairing.weylGroup.ofIdx P i * (RootPairing.weylGroup.ofIdx P i * w) = w := by
  rw [← mul_assoc, weylGroup_ofIdx_mul_self, one_mul]

/-- The root action intertwines multiplication by its reflection.
The root index `i` need not be simple. -/
theorem simpleWeylWord_mul_reflection (b : P.Base) (l : List b.support) (i : ι) :
    simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i =
      RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm (simpleWeylWord b l) i) *
        simpleWeylWord b l := by
  induction l with
  | nil => simp [simpleWeylWord]
  | cons j l ih =>
    simp only [simpleWeylWord, map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple,
      weylGroup_ofIdx_reflectionPerm]
    rw [mul_assoc, ih]
    simp only [mul_assoc, weylGroup_ofIdx_mul_cancel_left]

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- Simple-root exchange for every expression, with an explicit
deleted letter, its sign-crossing root, and the exact shortened length. -/
theorem simpleWeylWord_exchange (b : P.Base) (l : List b.support) (i : b.support)
    (hneg : b.height (P.weylGroupToPerm (simpleWeylWord b l) i) < 0) :
    ∃ (pre : List b.support) (j : b.support) (post : List b.support),
      l = pre ++ [j] ++ post ∧
      simpleWeylWord b post • P.root i = P.root j ∧
      simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i =
        simpleWeylWord b (pre ++ post) ∧
      (pre ++ post).length + 1 = l.length := by
  induction l with
  | nil =>
    have hn : b.height i < 0 := by simpa [simpleWeylWord] using hneg
    exact ((root_height_neg_iff_not_isPos b i).mp hn
      (b.isPos_of_mem_support i.property)).elim
  | cons j l ih =>
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)
    · have heq : P.weylGroupToPerm (simpleWeylWord b l) i = (j : ι) := by
        by_contra hne
        have hp := hpos.reflectionPerm j.property hne
        apply (root_height_neg_iff_not_isPos b _).mp hneg
        simpa only [simpleWeylWord, map_mul, Equiv.Perm.mul_apply,
          weylGroupToPerm_simple] using hp
      refine ⟨[], j, l, by simp, ?_, ?_, by simp⟩
      · rw [P.weylGroup_apply_root, heq]
      · have hintertwine := simpleWeylWord_mul_reflection b l i
        rw [heq] at hintertwine
        simpa only [simpleWeylWord, List.nil_append, mul_assoc,
          weylGroup_ofIdx_mul_cancel_left] using
            congrArg (fun w => RootPairing.weylGroup.ofIdx P j * w) hintertwine
    · obtain ⟨pre, k, post, hword, hroot, hprod, hlength⟩ :=
        ih ((root_height_neg_iff_not_isPos b _).mpr hpos)
      refine ⟨j :: pre, k, post, ?_, hroot, ?_, ?_⟩
      · simp only [List.cons_append, ← hword]
      · simpa only [simpleWeylWord, List.cons_append, mul_assoc] using
          congrArg (fun w => RootPairing.weylGroup.ofIdx P j * w) hprod
      · simp only [List.cons_append, List.length_cons]
        omega

/-- A negative simple-root image produces a word shorter by exactly one.
The preceding theorem identifies the removed position in the original word. -/
theorem Exchange.exists_simpleWeylWord_of_negative (b : P.Base)
    (l : List b.support) (i : b.support)
    (hneg : b.height (P.weylGroupToPerm (simpleWeylWord b l) i) < 0) :
    ∃ m : List b.support,
      simpleWeylWord b m = simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i ∧
      m.length + 1 = l.length := by
  obtain ⟨pre, j, post, _, _, hprod, hlength⟩ := simpleWeylWord_exchange b l i hneg
  exact ⟨pre ++ post, hprod.symm, hlength⟩

end ReductiveGroups
