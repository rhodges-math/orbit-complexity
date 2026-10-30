import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums

/-!
# Extending a positive root along an adjacent simple vertex

The result uses only the Cartan pairing and root sum. It works for
multiple bonds as well as simply-laced diagrams; the new vertex may touch
more than one vertex of the existing set.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- If the sum over `K` is a root, adding a new simple vertex adjacent
to `K` again yields a positive root. -/
theorem positiveRoot_sum_insert_of_adjacent (b : P.Base)
    (K : Finset b.support) (i : b.support) (hi : i ∉ K)
    (hroot : ∃ k : ι, P.root k = ∑ j ∈ K, P.root (j : ι))
    (hadj : ∃ j ∈ K, P.pairingIn ℤ (j : ι) (i : ι) ≠ 0) :
    ∃ k : ι, b.IsPos k ∧
      P.root k = ∑ j ∈ insert i K, P.root (j : ι) := by
  classical
  obtain ⟨k, hk⟩ := hroot
  obtain ⟨j, hj, hji⟩ := hadj
  have hrootSpan : (∑ x ∈ K, P.rootSpanMem ℤ (x : ι)) =
      P.rootSpanMem ℤ k := by
    apply Subtype.ext
    simpa using hk.symm
  have hle (x : b.support) (hx : x ∈ K) :
      P.pairingIn ℤ (x : ι) (i : ι) ≤ 0 :=
    b.pairingIn_le_zero_of_ne (fun h => hi (Subtype.ext h ▸ hx)) x.property i.property
  have hpairneg : P.pairingIn ℤ k (i : ι) < 0 := by
    have hsum : (∑ x ∈ K, P.pairingIn ℤ (x : ι) (i : ι)) =
        P.pairingIn ℤ k (i : ι) := by
      have h := congrArg (P.coroot'In ℤ (i : ι)) hrootSpan
      simpa only [map_sum, RootPairing.coroot'In_rootSpanMem_eq_pairingIn] using h
    rw [← hsum]
    have hlt : P.pairingIn ℤ (j : ι) (i : ι) < 0 := lt_of_le_of_ne (hle j hj) hji
    have hneg : (∑ x ∈ K, P.pairingIn ℤ (x : ι) (i : ι)) < 0 := by
      have h := Finset.sum_lt_sum (s := K)
        (f := fun x : b.support => P.pairingIn ℤ (x : ι) (i : ι))
        (g := fun _ => (0 : ℤ)) (fun x hx => hle x hx) ⟨j, hj, hlt⟩
      simpa using h
    exact hneg
  have hposk : b.IsPos k := by
    have hheight : (K.card : ℤ) = b.height k := by
      have h : (∑ x ∈ K, b.height (x : ι)) = b.height k := by
        simpa only [map_sum, rootLatticeHeight_root] using
          congrArg (rootLatticeHeight b) hrootSpan
      calc
        (K.card : ℤ) = ∑ _x ∈ K, (1 : ℤ) := by simp
        _ = ∑ x ∈ K, b.height (x : ι) := by
          apply Finset.sum_congr rfl
          intro x _
          exact (b.height_one_of_mem_support x.property).symm
        _ = b.height k := h
    change 0 < b.height k
    rw [← hheight]
    exact_mod_cast Finset.card_pos.mpr ⟨j, hj⟩
  have hnotneg : P.root k ≠ -P.root (i : ι) := by
    intro heq
    have hposi : b.IsPos (i : ι) := b.isPos_of_mem_support i.property
    have hspan : P.rootSpanMem ℤ k = -P.rootSpanMem ℤ (i : ι) := by
      apply Subtype.ext
      simpa using heq
    have hheight := congrArg (rootLatticeHeight b) hspan
    simp only [rootLatticeHeight_root, map_neg] at hheight
    have hkpos : 0 < b.height k := hposk
    have hipos : 0 < b.height (i : ι) := hposi
    omega
  obtain ⟨k', hk'⟩ := P.root_add_root_mem_of_pairingIn_neg hpairneg hnotneg
  refine ⟨k', ?_, ?_⟩
  · exact hposk.add (b.isPos_of_mem_support i.property) hk'
  · simpa [Finset.sum_insert hi, hk, add_comm] using hk'

end ReductiveGroups
