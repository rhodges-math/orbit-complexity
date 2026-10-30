import TauCeti.LinearAlgebra.RootSystem.BraidRelation
import Mathlib.Tactic.Module

/-! # Root sums for simple reflections of order six -/

namespace ReductiveGroups.OrderSix
open TauCeti
universe u v w x
variable {ι : Type u} {K : Type v} {M : Type w} {N : Type x}
  [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
  [Finite ι] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

private theorem order_six_cartan (i j : b.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx P i.val *
      RootPairing.weylGroup.ofIdx P j.val) = 6) :
    i ≠ j ∧
      ((P.pairingIn ℤ i.val j.val = -1 ∧ P.pairingIn ℤ j.val i.val = -3) ∨
       (P.pairingIn ℤ i.val j.val = -3 ∧ P.pairingIn ℤ j.val i.val = -1)) := by
  have hij : i ≠ j := by
    rintro rfl
    simp only [RootPairing.weylGroup.ofIdx_mul_self, orderOf_one] at h
    omega
  have hm := (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
    P b i j).symm.trans h
  rw [coxeterMatrixOfBase_apply] at hm
  have hc := cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  have hthree : P.pairingIn ℤ i.val j.val * P.pairingIn ℤ j.val i.val = 3 := by
    change b.cartanMatrix i j * b.cartanMatrix j i = 3
    rcases hc with hc | hc | hc | hc
    · rw [hc, coxeterOrder_zero] at hm
      omega
    · rw [hc, coxeterOrder_one] at hm
      omega
    · rw [hc, coxeterOrder_two] at hm
      omega
    · exact hc
  have hp := b.pairingIn_le_zero_of_ne (Subtype.coe_ne_coe.mpr hij)
    i.property j.property
  have hq := b.pairingIn_le_zero_of_ne (Subtype.coe_ne_coe.mpr hij.symm)
    j.property i.property
  have ht := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i.val j.val
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at ht
  refine ⟨hij, ?_⟩
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
    rcases ht with ⟨h₁, h₂⟩ <;> simp_all

omit [Finite ι] [P.IsCrystallographic] in
private theorem double_root (r : ι) :
    (2 : ℕ) • P.root r ≠ 0 ∧ (2 : ℕ) • P.root r ∉ Set.range P.root := by
  let : IsAddTorsionFree M := .of_isTorsionFree K M
  constructor
  · exact smul_ne_zero (by decide : (2 : ℕ) ≠ 0) (P.ne_zero r)
  · exact P.nsmul_notMem_range_root

private theorem order_six_double_sums (i j : b.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx P i.val *
      RootPairing.weylGroup.ofIdx P j.val) = 6) :
    let g := P.reflectionPerm i.val (P.reflectionPerm j.val i.val)
    (P.root g - P.root j.val ≠ 0 ∧
      P.root g - P.root j.val ∉ Set.range P.root) ∧
    (P.root g + P.root j.val ≠ 0 ∧
      P.root g + P.root j.val ∉ Set.range P.root) := by
  dsimp only
  obtain ⟨hij, hc | hc⟩ := order_six_cartan P b i j h
  · obtain ⟨hp, hq⟩ := hc
    have hp' : P.pairing i.val j.val = (-1 : K) := by
      rw [← P.algebraMap_pairingIn ℤ, hp]
      simp
    have hq' : P.pairing j.val i.val = (-3 : K) := by
      rw [← P.algebraMap_pairingIn ℤ, hq]
      simp
    have hg : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) =
        (2 : ℕ) • P.root i.val + P.root j.val := by
      simp only [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_smul]
      rw [hp', hq', P.pairing_same]
      module
    have ht : P.chainTopCoeff j.val i.val = 1 := by
      have hc := b.chainTopCoeff_eq_of_ne hij.symm
      rw [hp] at hc
      norm_num at hc
      exact_mod_cast hc
    have hs : P.root i.val + P.root j.val ∈ Set.range P.root := by
      simpa only [one_smul] using
        (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
          (b.linearIndependent_pair_of_ne hij.symm) (n := 1)).mpr (by omega)
    obtain ⟨r, hr⟩ := hs
    constructor
    · simpa only [hg, add_sub_cancel_right] using double_root P i.val
    · have he : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) +
          P.root j.val = (2 : ℕ) • P.root r := by
        rw [hg, hr]
        module
      simpa only [he] using double_root P r
  · obtain ⟨hp, hq⟩ := hc
    have hp' : P.pairing i.val j.val = (-3 : K) := by
      rw [← P.algebraMap_pairingIn ℤ, hp]
      simp
    have hq' : P.pairing j.val i.val = (-1 : K) := by
      rw [← P.algebraMap_pairingIn ℤ, hq]
      simp
    have hg : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) =
        (2 : ℕ) • P.root i.val + (3 : ℕ) • P.root j.val := by
      simp only [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_smul]
      rw [hp', hq', P.pairing_same]
      module
    have ht : P.chainTopCoeff j.val i.val = 3 := by
      have hc := b.chainTopCoeff_eq_of_ne hij.symm
      rw [hp] at hc
      norm_num at hc
      exact_mod_cast hc
    have hs (n : ℕ) (hn : n ≤ 3) :
        P.root i.val + n • P.root j.val ∈ Set.range P.root :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
        (b.linearIndependent_pair_of_ne hij.symm)).mpr (by omega)
    obtain ⟨r, hr⟩ := hs 1 (by omega)
    obtain ⟨s, hs⟩ := hs 2 (by omega)
    have hm : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) -
        P.root j.val = (2 : ℕ) • P.root r := by
      rw [hg, hr]
      module
    have ha : P.root (P.reflectionPerm i.val (P.reflectionPerm j.val i.val)) +
        P.root j.val = (2 : ℕ) • P.root s := by
      rw [hg, hs]
      module
    exact ⟨by simpa only [hm] using double_root P r,
      by simpa only [ha] using double_root P s⟩

/-- An order-six simple pair gives odd Cartan entries and four nonroot signed sums. -/
theorem order_six_simple_sums (i j : b.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx P i.val *
      RootPairing.weylGroup.ofIdx P j.val) = 6) :
    ((P.pairingIn ℤ i.val j.val = -1 ∧ P.pairingIn ℤ j.val i.val = -3) ∨
      (P.pairingIn ℤ i.val j.val = -3 ∧ P.pairingIn ℤ j.val i.val = -1)) ∧
    let g := P.reflectionPerm i.val (P.reflectionPerm j.val i.val)
    (P.root j.val + P.root g ≠ 0 ∧
      P.root j.val + P.root g ∉ Set.range P.root) ∧
    (P.root j.val - P.root g ≠ 0 ∧
      P.root j.val - P.root g ∉ Set.range P.root) ∧
    (-P.root j.val + P.root g ≠ 0 ∧
      -P.root j.val + P.root g ∉ Set.range P.root) ∧
    (-P.root j.val - P.root g ≠ 0 ∧
      -P.root j.val - P.root g ∉ Set.range P.root) := by
  refine ⟨(order_six_cartan P b i j h).2, ?_⟩
  obtain ⟨hm, ha⟩ := order_six_double_sums P b i j h
  have hn (z : M) (hz : z ≠ 0 ∧ z ∉ Set.range P.root) :
      -z ≠ 0 ∧ -z ∉ Set.range P.root :=
    ⟨neg_ne_zero.mpr hz.1, fun he => hz.2 (P.neg_mem_range_root_iff.mp he)⟩
  dsimp only at hm ha ⊢
  refine ⟨by simpa only [add_comm] using ha, ?_, ?_, ?_⟩
  · simpa only [neg_sub] using hn _ hm
  · simpa only [sub_eq_add_neg, add_comm] using hm
  · convert hn _ ha using 1 <;> abel

end ReductiveGroups.OrderSix
