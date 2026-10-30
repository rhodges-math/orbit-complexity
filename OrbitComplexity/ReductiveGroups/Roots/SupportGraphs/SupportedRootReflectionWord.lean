import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSupportStability

/-!
# Supported Root Reflection Word

Positive roots supported on a chosen simple subsystem are generated
by reflections in that subsystem. The proof descends the root
height, retaining the ambient root pairing and its simple coordinates. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq
open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- The inclusion is

```lean
P.pairingIn ℤ β (j : ι) ≤ 0
```
-/
theorem positiveRoot_pairing_nonpos_of_omitted
    (b : P.Base) (β : ι) (hβ : b.IsPos β) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0) :
    P.pairingIn ℤ β (j : ι) ≤ 0 := by
  rw [pairingIn_eq_sum_simpleRootCoeffInt b β j]
  apply Finset.sum_nonpos
  intro k _
  by_cases hk : k = j
  · subst k
    simp [hj]
  · exact mul_nonpos_of_nonneg_of_nonpos
      (simpleRootCoeffInt_nonneg_of_isPos b β hβ k)
      (b.pairingIn_le_zero_of_ne (fun h => hk (Subtype.ext h)) k.property j.property)

variable [P.IsReduced]

/-- Every positive root supported on J is a J-reflection word
applied to a simple root of J.  -/
theorem SupportedRootReflectionWord.positive_root_exists_simple_word
    (b : P.Base) (J : Set b.support) (β : ι)
    (hβ : b.IsPos β) (hsupport : simpleRootSupportInt b β ⊆ J) :
    ∃ word : List b.support, (∀ j ∈ word, j ∈ J) ∧
      ∃ i : b.support, i ∈ J ∧
        β = P.weylGroupToPerm (simpleWeylWord b word) (i : ι) := by
  generalize hn : (b.height β).natAbs = n
  induction n using Nat.strongRecOn generalizing β with
  | ind n ih =>
    obtain ⟨j, hj, hpair⟩ := hβ.exists_mem_support_pos_pairingIn
    have hp : 0 < P.pairingIn ℤ β j := (P.zero_lt_pairingIn_iff' ℤ).mp hpair
    let u : b.support := ⟨j, hj⟩
    have hu : u ∈ simpleRootSupportInt b β := by
      intro hz
      have hle := positiveRoot_pairing_nonpos_of_omitted b β hβ u hz
      change P.pairingIn ℤ β j ≤ 0 at hle
      omega
    have huJ : u ∈ J := hsupport hu
    rcases eq_or_ne β j with rfl | hne
    · exact ⟨[], by simp, u, huJ, rfl⟩
    · have hpos := hβ.reflectionPerm hj hne
      have hsupp := simpleRootSupport_reflection_subset b J β hsupport u huJ
      have hroot : P.root (P.reflectionPerm j β) =
          P.root β + (-P.pairingIn ℤ β j) • P.root j := by
        rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, neg_smul, sub_eq_add_neg]
      have hheight := b.height_add_zsmul hroot
      rw [b.height_one_of_mem_support hj] at hheight
      simp at hheight
      have hdec : (b.height (P.reflectionPerm j β)).natAbs < n := by
        have h₁ := Int.natAbs_of_nonneg (b.isPos_iff'.mp hpos)
        have h₂ := Int.natAbs_of_nonneg (b.isPos_iff'.mp hβ)
        omega
      obtain ⟨word, hword, i, hi, hrootWord⟩ :=
        ih _ hdec (P.reflectionPerm j β) hpos hsupp rfl
      refine ⟨u :: word, ?_, i, hi, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact huJ
        · exact hword k hk
      · change β = P.reflectionPerm j (P.weylGroupToPerm (simpleWeylWord b word) (i : ι))
        rw [← hrootWord]
        simp

end ReductiveGroups
