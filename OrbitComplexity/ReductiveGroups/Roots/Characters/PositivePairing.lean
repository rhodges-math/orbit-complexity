import OrbitComplexity.ReductiveGroups.Roots.Inversions.Inversions

/-! # The positive-root character and its simple-coroot weights -/

noncomputable section
namespace ReductiveGroups
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Roots
variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Fintype ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The positive roots have total simple-coroot pairing two. -/
theorem positive_pairing_sum (b : P.Base) (i : b.support) :
    ∑ r ∈ Finset.univ.filter b.IsPos, P.pairingIn ℤ r i.val = 2 := by
  classical
  let S := Finset.univ.filter b.IsPos
  let E := S.erase i.val
  have hi : b.IsPos i.val := b.isPos_of_mem_support i.property
  have hE (r : ι) : r ∈ E ↔ r ≠ i.val ∧ b.IsPos r := by simp [E, S]
  have hmap (r : ι) (hr : r ∈ E) : P.reflectionPerm i.val r ∈ E := by
    obtain ⟨hne, hpos⟩ := (hE r).mp hr
    apply (hE _).mpr
    refine ⟨?_, hpos.reflectionPerm i.property hne⟩
    intro he
    have hrneg : r = P.reflectionPerm i.val i.val := by
      simpa using congrArg (P.reflectionPerm i.val) he
    have hn : ¬ b.IsPos (P.reflectionPerm i.val i.val) := by
      exact (isPos_neg_index_iff b i.val).not.mpr (not_not.mpr hi)
    exact hn (hrneg ▸ hpos)
  have hneg (r : ι) :
      P.pairingIn ℤ (P.reflectionPerm i.val r) i.val =
        - P.pairingIn ℤ r i.val := by
    rw [← P.pairingIn_reflectionPerm ℤ i.val r i.val]
    exact P.pairingIn_reflectionPerm_self_right ℤ r i.val
  have hs : (∑ r ∈ E, P.pairingIn ℤ r i.val) =
      ∑ r ∈ E, -P.pairingIn ℤ r i.val := by
    refine Finset.sum_nbij' (P.reflectionPerm i.val) (P.reflectionPerm i.val)
      hmap hmap (fun r _ => P.reflectionPerm_involutive i.val r)
      (fun r _ => P.reflectionPerm_involutive i.val r) ?_
    intro r _
    rw [hneg, neg_neg]
  rw [Finset.sum_neg_distrib] at hs
  have hz : (∑ r ∈ E, P.pairingIn ℤ r i.val) = 0 := by omega
  have himem : i.val ∈ S := by simp [S, hi]
  have ht := Finset.add_sum_erase S (fun r => P.pairingIn ℤ r i.val) himem
  change (∑ r ∈ S, P.pairingIn ℤ r i.val) = 2
  rw [← ht]
  dsimp only [E] at hz
  simp only [P.pairingIn_same ℤ, hz, add_zero]

end Roots
end ReductiveGroups
