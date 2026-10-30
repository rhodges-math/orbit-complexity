import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBraidFourSquare

/-! # Four-term braid identities for the fixed simple representatives -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  (G : ReductiveGroupData K)

private theorem four_word_of_commutes {H : Type*} [Group H] (a b : H)
    (hc : Commute a (b * a * b⁻¹)) (hs : Commute a (b ^ 2)) :
    a * b * a * b = b * a * b * a := by
  calc
    _ = a * (b * a * b⁻¹) * b ^ 2 := by group
    _ = (b * a * b⁻¹) * a * b ^ 2 := by rw [hc.eq]
    _ = (b * a * b⁻¹) * b ^ 2 * a := by rw [mul_assoc, hs.eq, ← mul_assoc]
    _ = _ := by group

/-- A Cartan entry minus two gives the exact four-term braid in the full group. -/
theorem reflection_braid_four_of_pairing (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -2) :
    G.reflectionPoint i.val * G.reflectionPoint j.val *
        G.reflectionPoint i.val * G.reflectionPoint j.val =
      G.reflectionPoint j.val * G.reflectionPoint i.val *
        G.reflectionPoint j.val * G.reflectionPoint i.val :=
  four_word_of_commutes _ _ (G.reflection_conjugate_commute i j hp)
    (G.reflection_square_commute i j hp)

private theorem order_four_cartan (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 4) :
    (G.rootSystem.pairingIn ℤ i.val j.val = -2 ∧
      G.rootSystem.pairingIn ℤ j.val i.val = -1) ∨
    (G.rootSystem.pairingIn ℤ i.val j.val = -1 ∧
      G.rootSystem.pairingIn ℤ j.val i.val = -2) := by
  have hij : i ≠ j := by
    intro heq
    subst j
    have hf : (1 : ℕ) = 4 := by
      simpa only [RootPairing.weylGroup.ofIdx_mul_self, orderOf_one] using h
    omega
  have hm := (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
    G.rootSystem G.rootBase i j).symm.trans h
  rw [coxeterMatrixOfBase_apply] at hm
  have hc := cartanMatrix_mul_cartanMatrix_mem_of_ne G.rootSystem G.rootBase hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  have htwo : G.rootSystem.pairingIn ℤ i.val j.val *
      G.rootSystem.pairingIn ℤ j.val i.val = 2 := by
    rcases hc with hc | hc | hc | hc
    · rw [hc, coxeterOrder_zero] at hm
      omega
    · rw [hc, coxeterOrder_one] at hm
      omega
    · exact hc
    · rw [hc, coxeterOrder_three] at hm
      omega
  have ha : G.rootSystem.pairingIn ℤ i.val j.val ≤ 0 :=
    G.rootBase.cartanMatrix_le_zero_of_ne i j hij
  have hb : G.rootSystem.pairingIn ℤ j.val i.val ≤ 0 :=
    G.rootBase.cartanMatrix_le_zero_of_ne j i hij.symm
  have ha' : G.rootSystem.pairingIn ℤ i.val j.val ≤ -1 := by
    by_contra hnot
    have hz : G.rootSystem.pairingIn ℤ i.val j.val = 0 := by omega
    simp only [hz, zero_mul] at htwo
    omega
  have hb' : G.rootSystem.pairingIn ℤ j.val i.val ≤ -1 := by
    by_contra hnot
    have hz : G.rootSystem.pairingIn ℤ j.val i.val = 0 := by omega
    simp only [hz, mul_zero] at htwo
    omega
  have hlow : -2 ≤ G.rootSystem.pairingIn ℤ i.val j.val := by
    by_contra hnot
    have hmul := mul_nonneg
      (show 0 ≤ -G.rootSystem.pairingIn ℤ i.val j.val - 3 by omega)
      (show 0 ≤ -G.rootSystem.pairingIn ℤ j.val i.val - 1 by omega)
    nlinarith
  have hcase : G.rootSystem.pairingIn ℤ i.val j.val = -2 ∨
      G.rootSystem.pairingIn ℤ i.val j.val = -1 := by omega
  rcases hcase with hcase | hcase
  · exact Or.inl ⟨hcase, by rw [hcase] at htwo; omega⟩
  · exact Or.inr ⟨hcase, by rw [hcase] at htwo; omega⟩

/-- Coxeter order four gives the exact braid for the fixed simple representatives. -/
theorem reflection_braid_of_order_four (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 4) :
    G.reflectionPoint i.val * G.reflectionPoint j.val *
        G.reflectionPoint i.val * G.reflectionPoint j.val =
      G.reflectionPoint j.val * G.reflectionPoint i.val *
        G.reflectionPoint j.val * G.reflectionPoint i.val := by
  rcases order_four_cartan G i j h with hp | hp
  · exact G.reflection_braid_four_of_pairing i j hp.1
  · exact (G.reflection_braid_four_of_pairing j i hp.2).symm

end ReductiveGroups.ReductiveGroupData
