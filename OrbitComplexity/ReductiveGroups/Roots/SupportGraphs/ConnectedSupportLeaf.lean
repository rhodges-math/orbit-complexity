import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedSupportRoot

/-!
# Connected Support Leaf

A connected finite simple-root support has a leaf. The proof uses
root sums and integral Cartan pairings, without Dynkin classification. -/

noncomputable section
namespace ReductiveGroups
open scoped BigOperators
variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- Every connected nonempty set of simple vertices contains a vertex
with at most one neighbor in that set, including a singleton support. -/
theorem connectedSupport_exists_leaf (b : P.Base) (K : Finset b.support)
    (hK : K.Nonempty)
    (hconn : ((supportDynkinGraph b).induce (↑K : Set b.support)).Connected) :
    ∃ i ∈ K, ∀ j ∈ K, ∀ k ∈ K,
      (supportDynkinGraph b).Adj i j → (supportDynkinGraph b).Adj i k → j = k := by
  classical
  obtain ⟨β, _, hβ⟩ := connectedSupport_sum_isPositiveRoot b K hK hconn
  let l : List ι := K.toList.map Subtype.val
  have hsum : (l.map P.root).sum = P.root β := by
    change (List.map P.root (K.toList.map Subtype.val)).sum = P.root β
    rw [List.map_map, Finset.sum_map_toList]
    exact hβ.symm
  obtain ⟨r, hr, hpair⟩ := exists_mem_pairingIn_pos_of_root_sum_eq l β hsum
  obtain ⟨i, hi, hir⟩ := List.mem_map.mp hr
  have hiK : i ∈ K := Finset.mem_toList.mp hi
  subst r
  refine ⟨i, hiK, ?_⟩
  intro j hj k hk hij hik
  by_contra hjk
  have hij' := (supportDynkinGraph_adj_iff b i j).mp hij
  have hik' := (supportDynkinGraph_adj_iff b i k).mp hik
  let f : b.support → ℤ := fun a => P.pairingIn ℤ (a : ι) (i : ι)
  have hnonpos (a : b.support) (hai : a ≠ i) : f a ≤ 0 :=
    b.pairingIn_le_zero_of_ne (fun he => hai (Subtype.ext he)) a.property i.property
  have hjneg : f j ≤ -1 := by
    have hne := ((supportDynkinGraph_adj_iff b j i).mp hij.symm).2
    have hle := hnonpos j hij'.1.symm
    dsimp [f] at hle
    change P.pairingIn ℤ (j : ι) (i : ι) ≤ -1
    omega
  have hkneg : f k ≤ -1 := by
    have hne := ((supportDynkinGraph_adj_iff b k i).mp hik.symm).2
    have hle := hnonpos k hik'.1.symm
    dsimp [f] at hle
    change P.pairingIn ℤ (k : ι) (i : ι) ≤ -1
    omega
  have hrootSpan : (∑ a ∈ K, P.rootSpanMem ℤ (a : ι)) =
      P.rootSpanMem ℤ β := by
    apply Subtype.ext
    simpa using hβ.symm
  have hpairSum : ∑ a ∈ K, f a = P.pairingIn ℤ β (i : ι) := by
    have h := congrArg (P.coroot'In ℤ (i : ι)) hrootSpan
    simpa only [map_sum, RootPairing.coroot'In_rootSpanMem_eq_pairingIn, f] using h
  have hji : j ∈ K.erase i := Finset.mem_erase.mpr ⟨hij'.1.symm, hj⟩
  have hki : k ∈ (K.erase i).erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_erase.mpr ⟨hik'.1.symm, hk⟩⟩
  have hrest : ∑ a ∈ ((K.erase i).erase j).erase k, f a ≤ 0 := by
    apply Finset.sum_nonpos
    intro a ha
    have hai : a ≠ i :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2).1
    exact hnonpos a hai
  have heq : ∑ a ∈ K, f a =
      (∑ a ∈ ((K.erase i).erase j).erase k, f a) + f k + f j + 2 := by
    rw [← Finset.sum_erase_add _ _ hiK, ← Finset.sum_erase_add _ _ hji,
      ← Finset.sum_erase_add _ _ hki]
    simp only [f, RootPairing.pairingIn_same]
  omega

end ReductiveGroups
