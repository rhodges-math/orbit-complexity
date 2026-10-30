import TauCeti.LinearAlgebra.RootSystem.BraidRelation

/-! # Simple-root strings of Coxeter order three -/

noncomputable section
namespace ReductiveGroups
open TauCeti
universe u v w x
variable {ι : Type u} {K : Type v} {M : Type w} {N : Type x}
  [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
  [Finite ι] [P.IsCrystallographic] (b : P.Base)

private theorem order_three_cartan (i j : b.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx P i.val *
      RootPairing.weylGroup.ofIdx P j.val) = 3) :
    i ≠ j ∧ P.pairingIn ℤ i.val j.val = -1 ∧ P.pairingIn ℤ j.val i.val = -1 := by
  have hij : i ≠ j := by
    intro heq
    subst j
    have hf : (1 : ℕ) = 3 := by
      simpa only [RootPairing.weylGroup.ofIdx_mul_self, orderOf_one] using h
    omega
  have hm := (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
    P b i j).symm.trans h
  rw [coxeterMatrixOfBase_apply] at hm
  have hc := cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  have hone : b.cartanMatrix i j * b.cartanMatrix j i = 1 := by
    rcases hc with hc | hc | hc | hc
    · rw [hc, coxeterOrder_zero] at hm
      omega
    · exact hc
    · rw [hc, coxeterOrder_two] at hm
      omega
    · rw [hc, coxeterOrder_three] at hm
      omega
  exact ⟨hij, (cartanMatrix_mul_cartanMatrix_eq_one_iff P b hij).mp hone⟩

private theorem one_simple_string (i j : b.support) (hij : i ≠ j)
    (hp : P.pairingIn ℤ j.val i.val = -1) :
    (P.root j.val + P.root i.val ∈ Set.range P.root) ∧
    (P.root j.val + 2 • P.root i.val ≠ 0 ∧
      P.root j.val + 2 • P.root i.val ∉ Set.range P.root) := by
  have ht : P.chainTopCoeff i.val j.val = 1 := by
    have hc := b.chainTopCoeff_eq_of_ne hij
    rw [hp] at hc
    have hc' : (P.chainTopCoeff i.val j.val : ℤ) = 1 := by simpa using hc
    exact_mod_cast hc'
  have hli := b.linearIndependent_pair_of_ne hij
  have hsum : P.root j.val + P.root i.val ∈ Set.range P.root := by
    simpa only [one_smul] using
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli (n := 1)).mpr (by omega)
  have hn : P.root j.val + 2 • P.root i.val ∉ Set.range P.root := by
    intro hm
    have hk := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli (n := 2)).mp hm
    omega
  have hz : P.root j.val + 2 • P.root i.val ≠ 0 := by
    intro heq
    rw [two_smul] at heq
    have hc := congrArg (fun z : M => P.toLinearMap z (P.coroot i.val)) heq
    simp only [map_add, LinearMap.add_apply, map_zero, P.root_coroot_eq_pairing,
      P.pairing_same] at hc
    have hfield : P.pairing j.val i.val = (-1 : K) := by
      rw [← P.algebraMap_pairingIn ℤ j.val i.val, hp]
      simp
    rw [hfield] at hc
    norm_num at hc
  exact ⟨hsum, hz, hn⟩

/-- An order-three simple pair has Cartan entries minus one and first-order root strings. -/
theorem order_three_simple_root_strings (i j : b.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx P i.val *
      RootPairing.weylGroup.ofIdx P j.val) = 3) :
    (P.pairingIn ℤ i.val j.val = -1 ∧ P.pairingIn ℤ j.val i.val = -1) ∧
    (P.root i.val + P.root j.val ∈ Set.range P.root) ∧
    (P.root i.val - P.root j.val ≠ 0 ∧
      P.root i.val - P.root j.val ∉ Set.range P.root) ∧
    (P.root j.val + 2 • P.root i.val ≠ 0 ∧
      P.root j.val + 2 • P.root i.val ∉ Set.range P.root) ∧
    (P.root i.val + 2 • P.root j.val ≠ 0 ∧
      P.root i.val + 2 • P.root j.val ∉ Set.range P.root) := by
  obtain ⟨hij, hp, hq⟩ := order_three_cartan P b i j h
  obtain ⟨hsum, htwo⟩ := one_simple_string P b i j hij hq
  obtain ⟨_, htworev⟩ := one_simple_string P b j i hij.symm hp
  have hdiff : P.root i.val - P.root j.val ≠ 0 := by
    intro hz
    exact hij (Subtype.ext (P.root.injective (sub_eq_zero.mp hz)))
  exact ⟨⟨hp, hq⟩, by simpa only [add_comm] using hsum,
    ⟨hdiff, b.sub_notMem_range_root i.property j.property⟩, htwo, htworev⟩

end ReductiveGroups
