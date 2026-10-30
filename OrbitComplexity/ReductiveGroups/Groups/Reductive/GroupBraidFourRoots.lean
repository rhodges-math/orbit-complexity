import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import TauCeti.LinearAlgebra.RootSystem.BraidRelation

/-! # Sums of a long simple root and its reflected root -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A simple Cartan entry minus two gives two nonzero nonroot sums. -/
theorem orderFour_root_sums (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -2) :
    let r := G.rootSystem.reflectionPerm j.val i.val
    (G.rootSystem.root i.val + G.rootSystem.root r ≠ 0 ∧
      G.rootSystem.root i.val + G.rootSystem.root r ∉ Set.range G.rootSystem.root) ∧
    (G.rootSystem.root i.val - G.rootSystem.root r ≠ 0 ∧
      G.rootSystem.root i.val - G.rootSystem.root r ∉ Set.range G.rootSystem.root) := by
  let : IsAddTorsionFree (Module.Dual K G.cartan) := .of_isTorsionFree K _
  have hij : i ≠ j := by
    intro heq
    subst j
    norm_num only [RootPairing.pairingIn_same] at hp
  have hr : G.rootSystem.root (G.rootSystem.reflectionPerm j.val i.val) =
      G.rootSystem.root i.val + 2 • G.rootSystem.root j.val := by
    rw [G.rootSystem.root_reflectionPerm, G.rootSystem.reflection_apply_root' ℤ, hp]
    simp only [neg_smul, two_smul]
    abel
  have htop := G.rootBase.chainTopCoeff_eq_of_ne hij.symm
  rw [hp] at htop
  have hle : 1 ≤ G.rootSystem.chainTopCoeff j.val i.val := by omega
  have hsum : G.rootSystem.root i.val + G.rootSystem.root j.val ∈
      Set.range G.rootSystem.root := by
    simpa only [one_smul] using
      (G.rootSystem.root_add_nsmul_mem_range_iff_le_chainTopCoeff
        (G.rootBase.linearIndependent_pair_of_ne hij.symm) (n := 1)).mpr hle
  obtain ⟨t, ht⟩ := hsum
  have hplus : G.rootSystem.root i.val +
      G.rootSystem.root (G.rootSystem.reflectionPerm j.val i.val) =
      2 • G.rootSystem.root t := by
    rw [hr, ht, smul_add, two_nsmul, two_nsmul]
    abel
  have hminus : G.rootSystem.root i.val -
      G.rootSystem.root (G.rootSystem.reflectionPerm j.val i.val) =
      -(2 • G.rootSystem.root j.val) := by
    rw [hr]
    abel
  have ht0 : (2 : ℕ) • G.rootSystem.root t ≠ 0 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    exact smul_ne_zero (by norm_num) (G.rootSystem.ne_zero t)
  have hj0 : (2 : ℕ) • G.rootSystem.root j.val ≠ 0 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    exact smul_ne_zero (by norm_num) (G.rootSystem.ne_zero j.val)
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rwa [hplus]
  · rw [hplus]
    exact G.rootSystem.nsmul_notMem_range_root
  · rw [hminus]
    exact neg_ne_zero.mpr hj0
  · rw [hminus, G.rootSystem.neg_mem_range_root_iff]
    exact G.rootSystem.nsmul_notMem_range_root

end ReductiveGroups.ReductiveGroupData
