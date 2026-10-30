import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveCartanVector
import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedSupportRoot

/-!
# Isolation of a triple Cartan bond

The finite positive root form rules out a third vertex attached to either
endpoint of a bond with Cartan entries `-3` and `-1`. We use three-coordinate nonnegative vectors,
without asserting that those vectors are themselves roots.
-/

noncomputable section
namespace ReductiveGroups

attribute [local instance] Classical.decEq
open Sym2
open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] in
private theorem three_weighted_cartan_sum (b : P.Base)
    (a d c j : b.support) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
    (x y z : ℤ) :
    (∑ i : b.support,
      (if i = a then x else if i = d then y else if i = c then z else 0) *
        P.pairingIn ℤ (i : ι) (j : ι)) =
      x * P.pairingIn ℤ (a : ι) (j : ι) +
        y * P.pairingIn ℤ (d : ι) (j : ι) +
        z * P.pairingIn ℤ (c : ι) (j : ι) := by
  classical
  calc
    _ = ∑ i : b.support,
        ((if i = a then x * P.pairingIn ℤ (i : ι) (j : ι) else 0) +
        (if i = d then y * P.pairingIn ℤ (i : ι) (j : ι) else 0) +
        (if i = c then z * P.pairingIn ℤ (i : ι) (j : ι) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hia : i = a <;> by_cases hid : i = d <;>
            by_cases hic : i = c <;> simp_all
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

omit [P.IsReduced] in
private theorem three_weighted_cartan_obstruction (b : P.Base)
    (a d c : b.support) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
    (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ha : x * 2 + y * P.pairingIn ℤ (d : ι) (a : ι) +
      z * P.pairingIn ℤ (c : ι) (a : ι) ≤ 0)
    (hd : x * P.pairingIn ℤ (a : ι) (d : ι) + y * 2 +
      z * P.pairingIn ℤ (c : ι) (d : ι) ≤ 0)
    (hc : x * P.pairingIn ℤ (a : ι) (c : ι) +
      y * P.pairingIn ℤ (d : ι) (c : ι) + z * 2 ≤ 0) : False := by
  let w : b.support → ℤ :=
    fun i => if i = a then x else if i = d then y else if i = c then z else 0
  have hw (i : b.support) : 0 ≤ w i := by
    dsimp [w]
    split_ifs <;> omega
  have hwa : 0 < w a := by simp [w, hx]
  obtain ⟨j, hj, hpos⟩ :=
    SimpleCartan.pairing_of_nonnegative_coefficients b w hw ⟨a, hwa⟩
  have hja : j = a ∨ j = d ∨ j = c := by
    by_contra hh
    have hneA : j ≠ a := by intro he; exact hh (Or.inl he)
    have hneD : j ≠ d := by intro he; exact hh (Or.inr (Or.inl he))
    have hneC : j ≠ c := by intro he; exact hh (Or.inr (Or.inr he))
    simp [w, hneA, hneD, hneC] at hj
  rcases hja with hja | hjd | hjc
  · rw [hja, three_weighted_cartan_sum b a d c a had hac hdc,
      RootPairing.pairingIn_same] at hpos
    omega
  · rw [hjd, three_weighted_cartan_sum b a d c d had hac hdc,
      RootPairing.pairingIn_same] at hpos
    omega
  · rw [hjc, three_weighted_cartan_sum b a d c c had hac hdc,
      RootPairing.pairingIn_same] at hpos
    omega

omit [P.IsReduced] in
/-- A triple bond has no third neighbor at its `-1` endpoint. -/
theorem tripleBond_no_neighbor_at_second (b : P.Base)
    (a d c : b.support) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
    (had3 : P.pairingIn ℤ (a : ι) (d : ι) = -3)
    (hda1 : P.pairingIn ℤ (d : ι) (a : ι) = -1)
    (hdcAdj : (supportDynkinGraph b).Adj d c) : False := by
  have hca : P.pairingIn ℤ (c : ι) (a : ι) ≤ 0 :=
    b.pairingIn_le_zero_of_ne
      (fun he => hac (Subtype.ext he).symm) c.property a.property
  have hac' : P.pairingIn ℤ (a : ι) (c : ι) ≤ 0 :=
    b.pairingIn_le_zero_of_ne
      (fun he => hac (Subtype.ext he)) a.property c.property
  have hcd : P.pairingIn ℤ (c : ι) (d : ι) ≤ -1 := by
    have hle := b.pairingIn_le_zero_of_ne
      (fun he => hdc (Subtype.ext he).symm) c.property d.property
    have hne := ((supportDynkinGraph_adj_iff b c d).mp hdcAdj.symm).2
    omega
  have hdc' : P.pairingIn ℤ (d : ι) (c : ι) ≤ -1 := by
    have hle := b.pairingIn_le_zero_of_ne
      (fun he => hdc (Subtype.ext he)) d.property c.property
    have hne := ((supportDynkinGraph_adj_iff b d c).mp hdcAdj).2
    omega
  exact three_weighted_cartan_obstruction b a d c had hac hdc
    1 2 1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

omit [P.IsReduced] in
/-- A triple bond has no third neighbor at its `-3` endpoint. -/
theorem tripleBond_no_neighbor_at_first (b : P.Base)
    (a d c : b.support) (had : a ≠ d) (hac : a ≠ c) (hdc : d ≠ c)
    (had3 : P.pairingIn ℤ (a : ι) (d : ι) = -3)
    (hda1 : P.pairingIn ℤ (d : ι) (a : ι) = -1)
    (hacAdj : (supportDynkinGraph b).Adj a c) : False := by
  have hca : P.pairingIn ℤ (c : ι) (a : ι) ≤ -1 := by
    have hle := b.pairingIn_le_zero_of_ne
      (fun he => hac (Subtype.ext he).symm) c.property a.property
    have hne := ((supportDynkinGraph_adj_iff b c a).mp hacAdj.symm).2
    omega
  have hac' : P.pairingIn ℤ (a : ι) (c : ι) ≤ -1 := by
    have hle := b.pairingIn_le_zero_of_ne
      (fun he => hac (Subtype.ext he)) a.property c.property
    have hne := ((supportDynkinGraph_adj_iff b a c).mp hacAdj).2
    omega
  have hcd : P.pairingIn ℤ (c : ι) (d : ι) ≤ 0 :=
    b.pairingIn_le_zero_of_ne
      (fun he => hdc (Subtype.ext he).symm) c.property d.property
  have hdc' : P.pairingIn ℤ (d : ι) (c : ι) ≤ 0 :=
    b.pairingIn_le_zero_of_ne
      (fun he => hdc (Subtype.ext he)) d.property c.property
  exact three_weighted_cartan_obstruction b a d c had hac hdc
    2 3 1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

omit [P.IsReduced] in
/-- A connected positive-root support containing both endpoints of a
triple bond consists of exactly those two simple vertices. -/
theorem positiveRoot_triple_bond_support_eq_pair (b : P.Base)
    (β : ι) (hβ : b.IsPos β)
    (a d : b.support)
    (ha : a ∈ simpleRootSupportInt b β)
    (hd : d ∈ simpleRootSupportInt b β)
    (had : a ≠ d)
    (had3 : P.pairingIn ℤ (a : ι) (d : ι) = -3)
    (hda1 : P.pairingIn ℤ (d : ι) (a : ι) = -1) :
    simpleRootSupportInt b β = {a, d} := by
  let G := supportDynkinGraph b
  let S := simpleRootSupportInt b β
  let H := G.induce S
  have hconn : H.Connected := positiveRoot_simpleSupport_connected b β hβ
  have honlyA (v : b.support) (hv : G.Adj a v) : v = d := by
    by_contra hne
    exact tripleBond_no_neighbor_at_first b a d v had hv.ne (Ne.symm hne)
      had3 hda1 hv
  have honlyD (v : b.support) (hv : G.Adj d v) : v = a := by
    by_contra hne
    exact tripleBond_no_neighbor_at_second b a d v had (Ne.symm hne) hv.ne
      had3 hda1 hv
  have hreach (v : S) : v.1 = a ∨ v.1 = d := by
    have hr : Relation.ReflTransGen H.Adj (⟨a, ha⟩ : S) v :=
      (H.reachable_iff_reflTransGen _ _).mp
        (hconn.preconnected (⟨a, ha⟩ : S) v)
    induction hr with
    | refl => exact Or.inl rfl
    | @tail u w _ huw ih =>
      rcases ih with hua | hud
      · right
        have h : G.Adj a w.1 := hua ▸ huw
        exact honlyA w.1 h
      · left
        have h : G.Adj d w.1 := hud ▸ huw
        exact honlyD w.1 h
  ext v
  constructor
  · intro hv
    rcases hreach ⟨v, hv⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hv
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv.elim
      (fun h => h ▸ ha) (fun h => h ▸ hd)

end ReductiveGroups
