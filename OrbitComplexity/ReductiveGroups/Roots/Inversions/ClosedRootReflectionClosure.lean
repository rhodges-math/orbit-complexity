import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Closed Root Reflection Closure

A closed asymmetric root subset contains the reflection of each member
whose pairing with a fixed member is negative. -/

noncomputable section
namespace ReductiveGroups

open RootPairing

universe u v w₁ w₂
variable {ι : Type u} {R : Type v} {M : Type w₁} {N : Type w₂}
  [Finite ι] [AddCommGroup M] [AddCommGroup N]
  [Field R] [CharZero R] [Module R M] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]

/-- If a root subset is closed under root sums and excludes opposite pairs,
reflection in one of its roots preserves its negative-pairing members. -/
theorem ClosedRootReflectionClosure.root_reflection_mem_of_pairing_neg
    (s : Set ι)
    (hopp : ∀ i ∈ s, ∀ j ∈ s, P.root i ≠ -P.root j)
    (hclosed : ∀ i ∈ s, ∀ j ∈ s, ∀ k, P.root k = P.root i + P.root j → k ∈ s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hneg : P.pairingIn ℤ j i < 0) : P.reflectionPerm i j ∈ s := by
  classical
  have hij : i ≠ j := by
    intro heq
    subst j
    simp at hneg
  have hnotopp : P.root i ≠ -P.root j := hopp i hi j hj
  have hlin : LinearIndependent R ![P.root i, P.root j] :=
    RootPairing.IsReduced.linearIndependent P hij hnotopp
  have htop : -P.pairingIn ℤ j i ≤ (P.chainTopCoeff i j : ℤ) := by
    have hchain := P.chainTopCoeff_sub_chainBotCoeff hlin
    omega
  have hstep (k : ℕ) (hk : k ≤ P.chainTopCoeff i j) :
      ∃ j' ∈ s, P.root j' = P.root j + k • P.root i := by
    induction k with
    | zero => exact ⟨j, hj, by simp⟩
    | succ k ih =>
      have hk' : k ≤ P.chainTopCoeff i j := by omega
      obtain ⟨j', hj', heq⟩ := ih hk'
      have hrange : P.root j + (k + 1) • P.root i ∈ Set.range P.root :=
        (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mpr hk
      obtain ⟨j'', hj''⟩ := hrange
      refine ⟨j'', hclosed j' hj' i hi j'' ?_, hj''⟩
      rw [hj'', heq]
      simp only [succ_nsmul]
      abel
  let k := (-P.pairingIn ℤ j i).toNat
  have hk : k ≤ P.chainTopCoeff i j := by
    have hkn : (k : ℤ) = -P.pairingIn ℤ j i := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨j', hj', heq⟩ := hstep k hk
  have href : P.root (P.reflectionPerm i j) = P.root j + k • P.root i := by
    have hkn : (k : ℤ) = -P.pairingIn ℤ j i := Int.toNat_of_nonneg (by omega)
    rw [P.root_reflectionPerm, P.reflection_apply_root]
    rw [← P.algebraMap_pairingIn ℤ]
    simpa [sub_eq_add_neg, ← neg_smul, ← map_neg, Nat.cast_smul_eq_nsmul] using
      congrArg (fun z : R => z • P.root i) (show (-(P.pairingIn ℤ j i : ℤ) : R) = (k : R) by
        exact_mod_cast hkn.symm)
  have : P.reflectionPerm i j = j' := P.root.injective (href.trans heq.symm)
  simpa [this] using hj'

end ReductiveGroups
