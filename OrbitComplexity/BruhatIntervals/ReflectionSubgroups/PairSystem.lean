import OrbitComplexity.BruhatIntervals.Realizations.Roots
import OrbitComplexity.BruhatIntervals.Order.Basic
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Coxeter systems from a generating pair of involutions

Two distinct nonidentity involutions generating a group give a rank-two Coxeter system. Its
off-diagonal exponent is the order of their product, including exponent zero for infinite order.
The construction compares the presented Coxeter group with the dihedral group.

## Main results

* `exists_pair_coxeter`: a generating pair of involutions is the simple pair of a Coxeter system.

## References

* M. Dyer, *Reflection Subgroups of Coxeter Systems*, Journal of Algebra 135 (1990), Section 3.
-/

namespace BruhatIntervals

private def pairMatrix (n : ℕ) (hne : n ≠ 1) : CoxeterMatrix Bool where
  M i j := if i = j then 1 else n
  isSymm := by
    apply Matrix.ext
    intro i j
    change (if j = i then 1 else n) = if i = j then 1 else n
    simp only [eq_comm]
  diagonal i := ite_eq_left rfl
  off_diagonal i j hij := by simpa only [ite_eq_right hij] using hne

private theorem cast_one_power {G : Type*} [Group G] {n : ℕ} (g : G)
    (horder : orderOf g = n) : g ^ (ZMod.cast (1 : ZMod n) : ℤ) = g := by
  calc
    g ^ (ZMod.cast (1 : ZMod n) : ℤ) = g ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, horder, ← ZMod.intCast_eq_intCast_iff,
        ZMod.intCast_zmod_cast, Int.cast_one]
    _ = g := zpow_one g

private theorem recognition_simple {G : Type*} [Group G] {r s : G} {n : ℕ}
    (hr : r * r = 1) (hs : s * s = 1) (hr1 : r ≠ 1) (hs1 : s ≠ 1)
    (hn : orderOf (r * s) = n) (hgen : Subgroup.closure ({r, s} : Set G) = ⊤) :
    TauCeti.dihedralGroupMulEquiv hr hs hr1 hs1 hn hgen (DihedralGroup.sr 0) = r ∧
      TauCeti.dihedralGroupMulEquiv hr hs hr1 hs1 hn hgen (DihedralGroup.sr 1) = s := by
  constructor
  · rw [TauCeti.dihedralGroupMulEquiv_apply, TauCeti.dihedralHom_sr, ZMod.cast_zero,
      zpow_zero, mul_one]
  · rw [TauCeti.dihedralGroupMulEquiv_apply, TauCeti.dihedralHom_sr,
      cast_one_power _ hn, ← mul_assoc, hr, one_mul]

/-- Two distinct nonidentity involutions generating a group are the simple generators of a
rank-two Coxeter system with exponent equal to the order of their product. -/
theorem exists_pair_coxeter {G : Type*} [Group G] (r s : G)
    (hr : r * r = 1) (hs : s * s = 1) (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hrs : r ≠ s)
    (hgen : Subgroup.closure ({r, s} : Set G) = ⊤) :
    ∃ M : CoxeterMatrix Bool, ∃ cs : CoxeterSystem M G,
      cs.simple false = r ∧ cs.simple true = s ∧ M false true = orderOf (r * s) := by
  classical
  let n := orderOf (r * s)
  have hn : n ≠ 1 := by
    intro h
    have hprod := orderOf_eq_one_iff.mp h
    apply hrs
    calc
      r = r * (s * s) := by rw [hs, mul_one]
      _ = s := by rw [← mul_assoc, hprod, one_mul]
  let M := pairMatrix n hn
  let base := M.toCoxeterSystem
  let f : Bool → G := fun i => if i then s else r
  have hrel : M.IsLiftable f := by
    intro i j
    cases i <;> cases j
    · simpa [f, M, pairMatrix] using hr
    · exact pow_orderOf_eq_one (r * s)
    · have hinv : s * r = (r * s)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hr, inv_eq_of_mul_eq_one_right hs]
      change (s * r) ^ n = 1
      rw [hinv, inv_pow, pow_orderOf_eq_one, inv_one]
    · simpa [f, M, pairMatrix] using hs
  let lift := base.lift ⟨f, hrel⟩
  have hmap (i : Bool) : lift (base.simple i) = f i := base.lift_apply_simple hrel i
  have horder : orderOf (base.simple false * base.simple true) = n := by
    apply Nat.dvd_antisymm
    · have hpow := base.simple_mul_simple_pow false true
      exact orderOf_dvd_of_pow_eq_one hpow
    · have hdiv := orderOf_map_dvd lift (base.simple false * base.simple true)
      simpa [map_mul, hmap, f, n] using hdiv
  have hbasegen : Subgroup.closure
      ({base.simple false, base.simple true} : Set M.Group) = ⊤ := by
    have hrange : Set.range base.simple = {base.simple false, base.simple true} := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        cases i <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or]
      · rintro (rfl | rfl)
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
    rw [← hrange]
    exact base.subgroup_closure_range_simple
  have hbase1 (i : Bool) : base.simple i ≠ 1 := by
    intro heq
    have hlen := base.length_simple i
    rw [heq, base.length_one] at hlen
    omega
  let source := TauCeti.dihedralGroupMulEquiv (base.simple_mul_simple_self false)
    (base.simple_mul_simple_self true) (hbase1 false) (hbase1 true) horder hbasegen
  let target := TauCeti.dihedralGroupMulEquiv hr hs hr1 hs1 (rfl : orderOf (r * s) = n) hgen
  have hsource := recognition_simple (base.simple_mul_simple_self false)
    (base.simple_mul_simple_self true) (hbase1 false) (hbase1 true) horder hbasegen
  have htarget := recognition_simple hr hs hr1 hs1 (rfl : orderOf (r * s) = n) hgen
  change source (DihedralGroup.sr 0) = base.simple false ∧
    source (DihedralGroup.sr 1) = base.simple true at hsource
  change target (DihedralGroup.sr 0) = r ∧ target (DihedralGroup.sr 1) = s at htarget
  refine ⟨M, base.map (source.symm.trans target), ?_, ?_, rfl⟩
  · rw [CoxeterSystem.map_simple, ← hsource.1]
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using htarget.1
  · rw [CoxeterSystem.map_simple, ← hsource.2]
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using htarget.2

end BruhatIntervals
