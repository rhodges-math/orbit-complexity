import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanRootGrowth
import OrbitComplexity.ReductiveGroups.Roots.Supports.DistinctWordSupport

/-!
# Coefficient growth across a multiple bond

The local inequality below is the Cartan step in the opposite-crossing argument. A positive root
reflected at an omitted
simple vertex acquires at least the contribution from any one already
occupied neighboring vertex; other nonnegative coefficients cannot
cancel it.
-/

noncomputable section
namespace ReductiveGroups

open scoped BigOperators
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- A reflection at an omitted simple root acquires at least the
weighted contribution from any chosen distinct occupied vertex. This
uses integral simple coordinates and Cartan pairings. -/
theorem BooleanBondOrder.omitted_coefficient_ge_bond_contribution
    (b : P.Base) (β : ι) (hβ : b.IsPos β)
    (i j : b.support)
    (hj : simpleRootCoeffInt b β j = 0) :
    -simpleRootCoeffInt b β i *
        P.pairingIn ℤ (i : ι) (j : ι) ≤
      simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j := by
  have hcoeff (k : b.support) : 0 ≤ simpleRootCoeffInt b β k :=
    simpleRootCoeffInt_nonneg_of_isPos b β hβ k
  have hpair : P.pairingIn ℤ β (j : ι) ≤
      simpleRootCoeffInt b β i *
        P.pairingIn ℤ (i : ι) (j : ι) := by
    rw [pairingIn_eq_sum_simpleRootCoeffInt b β j]
    have hrest :
        (∑ k ∈ (Finset.univ : Finset b.support).erase i,
          simpleRootCoeffInt b β k *
            P.pairingIn ℤ (k : ι) (j : ι)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      by_cases hkj : k = j
      · subst k
        simp [hj]
      · have hcart := b.pairingIn_le_zero_of_ne
          (fun he => hkj (Subtype.ext he)) k.property j.property
        exact mul_nonpos_of_nonneg_of_nonpos (hcoeff k) hcart
    have hi : i ∈ (Finset.univ : Finset b.support) := Finset.mem_univ i
    rw [← Finset.sum_erase_add _ _ hi]
    omega
  rw [simpleRootCoeffInt_reflection, ite_eq_left rfl, hj]
  nlinarith

variable [P.IsReduced]

/-- If the letter `j` occurs before the letter `q` in a distinct
left-to-right simple word, then the final coefficient at `j` dominates
the Cartan contribution of the final coefficient at `q`.
The word acts from right to left. All letters before `j` omit both
`j` and `q`; the suffix and the initial simple root omit `j`. -/
theorem SimpleWeylWord.bond_coefficient_lower_of_order
    (b : P.Base) (L M : List b.support) (i j q : b.support)
    (hi : i ∉ L ++ j :: M)
    (hjL : j ∉ L) (hjM : j ∉ M)
    (hqL : q ∉ L) (hjq : j ≠ q) :
    -simpleRootCoeffInt b
        (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: M)) i) q *
        P.pairingIn ℤ (q : ι) (j : ι) ≤
      simpleRootCoeffInt b
        (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: M)) i) j := by
  have hiM : i ∉ M := by
    intro h
    exact hi (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h)))
  have hij : j ≠ i := by
    intro h
    exact hi (List.mem_append.mpr (Or.inr (by simp [h])))
  let δ : ι := P.weylGroupToPerm (simpleWeylWord b M) i
  let ρ : ι := P.reflectionPerm (j : ι) δ
  let σ : ι := P.weylGroupToPerm (simpleWeylWord b (L ++ j :: M)) i
  have hδpos : b.IsPos δ :=
    simpleWeylWord_isPos_of_notMem_ambient b M hiM
  have hδj : simpleRootCoeffInt b δ j = 0 :=
    SimpleWeylWord.simple_coeff_zero_of_omitted b M i j hij hjM
  have hσ : σ = P.weylGroupToPerm (simpleWeylWord b L) ρ := by
    dsimp [σ, ρ, δ]
    rw [simpleWeylWord_append]
    change P.weylGroupToPerm
      (simpleWeylWord b L *
        (RootPairing.weylGroup.ofIdx P j * simpleWeylWord b M)) i = _
    rw [map_mul, Equiv.Perm.mul_apply, map_mul, Equiv.Perm.mul_apply,
      weylGroupToPerm_simple]
    rfl
  have hσj : simpleRootCoeffInt b σ j = simpleRootCoeffInt b ρ j := by
    rw [hσ]
    exact SimpleWeylWord.preserves_omitted_coefficient b L ρ j hjL
  have hσq : simpleRootCoeffInt b σ q = simpleRootCoeffInt b δ q := by
    rw [hσ, SimpleWeylWord.preserves_omitted_coefficient b L ρ q hqL]
    rw [simpleRootCoeffInt_reflection, ite_eq_right hjq, mul_zero, sub_zero]
  have hbound := BooleanBondOrder.omitted_coefficient_ge_bond_contribution
    b δ hδpos q j hδj
  rw [← hσj, ← hσq] at hbound
  exact hbound

end ReductiveGroups
