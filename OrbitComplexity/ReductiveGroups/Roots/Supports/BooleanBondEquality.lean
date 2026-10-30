import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanOppositeCrossing
import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanSupportLocalization

/-!
# Exact coefficient propagation across an occupied Boolean bond

An effective reflection at a newly occupied simple root has exactly
one neighbor in the old connected support. Thus its new coefficient
is the old neighboring coefficient times the Cartan weight.
-/

noncomputable section
namespace ReductiveGroups

attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- If `j` precedes `q` in the prefix action and both survive in the
final root, the newly created `j` coefficient equals the exact
Cartan-weighted `q` coefficient. Other old support vertices are
excluded by the proved unique-neighbor growth theorem. -/
theorem SimpleWeylWord.bond_coefficient_eq_of_order
    (b : P.Base) (L T : List b.support) (i j q : b.support)
    (hi : i ∉ L ++ j :: T)
    (hjL : j ∉ L) (hjT : j ∉ T)
    (hqL : q ∉ L) (hjq : j ≠ q)
    (hpair : P.pairingIn ℤ (q : ι) (j : ι) ≠ 0)
    (hjfinal : simpleRootCoeffInt b
      (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: T)) i) j ≠ 0)
    (hqfinal : simpleRootCoeffInt b
      (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: T)) i) q ≠ 0) :
    simpleRootCoeffInt b
        (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: T)) i) j =
      -simpleRootCoeffInt b
        (P.weylGroupToPerm (simpleWeylWord b (L ++ j :: T)) i) q *
        P.pairingIn ℤ (q : ι) (j : ι) := by
  have hiT : i ∉ T := by
    intro h
    exact hi (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h)))
  have hij : j ≠ i := by
    intro h
    exact hi (List.mem_append.mpr (Or.inr (by simp [h])))
  let δ : ι := P.weylGroupToPerm (simpleWeylWord b T) i
  let ρ : ι := P.reflectionPerm (j : ι) δ
  let σ : ι := P.weylGroupToPerm (simpleWeylWord b (L ++ j :: T)) i
  have hδpos : b.IsPos δ :=
    simpleWeylWord_isPos_of_notMem_ambient b T hiT
  have hδj : simpleRootCoeffInt b δ j = 0 :=
    SimpleWeylWord.simple_coeff_zero_of_omitted b T i j hij hjT
  have hσ : σ = P.weylGroupToPerm (simpleWeylWord b L) ρ := by
    dsimp [σ, ρ, δ]
    rw [simpleWeylWord_append]
    change P.weylGroupToPerm
      (simpleWeylWord b L *
        (RootPairing.weylGroup.ofIdx P j * simpleWeylWord b T)) i = _
    rw [map_mul, Equiv.Perm.mul_apply, map_mul, Equiv.Perm.mul_apply,
      weylGroupToPerm_simple]
    rfl
  have hσj : simpleRootCoeffInt b σ j = simpleRootCoeffInt b ρ j := by
    rw [hσ]
    exact SimpleWeylWord.preserves_omitted_coefficient b L ρ j hjL
  have hσq : simpleRootCoeffInt b σ q = simpleRootCoeffInt b δ q := by
    rw [hσ, SimpleWeylWord.preserves_omitted_coefficient b L ρ q hqL]
    rw [simpleRootCoeffInt_reflection, ite_eq_right hjq, mul_zero, sub_zero]
  have hδq : simpleRootCoeffInt b δ q ≠ 0 := by
    rw [← hσq]
    exact hqfinal
  have hmove : ρ ≠ δ := by
    intro he
    have hh : simpleRootCoeffInt b σ j = 0 := by
      rw [hσj, he]
      exact hδj
    exact hjfinal hh
  obtain ⟨k, hk, _, huniq, _, _, _, hnew⟩ :=
    booleanRootGrowth_reflection b δ hδpos j hδj hmove
  have hqSupp : q ∈ simpleRootSupportInt b δ := hδq
  have hkq : q = k := huniq q hqSupp hpair
  change simpleRootCoeffInt b σ j =
    -simpleRootCoeffInt b σ q * P.pairingIn ℤ (q : ι) (j : ι)
  rw [hσj, hσq]
  simpa only [← hkq] using hnew

/-- Exact Cartan-weighted coefficient propagation across an occupied
bond in one left inversion of a distinct word. -/
theorem LeftRootInversion.bond_coefficient_eq_of_word_order
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (β : ι) (hβ : P.root β ∈
      leftRootInversions b (simpleWeylWord b l))
    (j q : b.support) (hjq : j ≠ q)
    (hpair : P.pairingIn ℤ (q : ι) (j : ι) ≠ 0)
    (hjβ : simpleRootCoeffInt b β j ≠ 0)
    (hqβ : simpleRootCoeffInt b β q ≠ 0)
    (horder : l.idxOf j < l.idxOf q) :
    simpleRootCoeffInt b β j =
      -simpleRootCoeffInt b β q *
        P.pairingIn ℤ (q : ι) (j : ι) := by
  obtain ⟨L, i, T, hword, hβeq⟩ :=
    leftRootInversion_exists_word_occurrence b l hl β hβ
  have hqEither : q = i ∨ q ∈ L := by
    have hqSupp : q ∈ simpleRootSupportInt b β := hqβ
    rw [hβeq] at hqSupp
    have h := simpleWeylWord_simple_support_subset b L i hqSupp
    simpa only [Set.mem_insert_iff, Set.mem_ofPred_eq] using h
  obtain ⟨U, V, hL, hqU⟩ :=
    nodup_word_bond_order_in_occurrence l L T i j q hl hword
      horder hqEither
  have hiL : i ∉ L := by
    rw [hword] at hl
    intro hi
    exact (List.nodup_append.mp hl).2.2 i hi i (by simp) rfl
  have hLnodup : L.Nodup := by
    rw [hword] at hl
    exact (List.nodup_append.mp hl).1
  have hjU : j ∉ U := by
    rw [hL] at hLnodup
    intro hj
    exact (List.nodup_append.mp hLnodup).2.2 j hj j (by simp) rfl
  have hjV : j ∉ V := by
    rw [hL] at hLnodup
    exact (List.nodup_cons.mp (List.nodup_append.mp hLnodup).2.1).1
  have hiUV : i ∉ U ++ j :: V := by simpa only [← hL] using hiL
  rw [hβeq, hL] at hjβ hqβ ⊢
  exact SimpleWeylWord.bond_coefficient_eq_of_order
    b U V i j q hiUV hjU hjV hqU hjq hpair hjβ hqβ

/-- Across a simple bond, every occupied coefficient of one
Boolean inversion agrees with its neighbor, irrespective of which
letter precedes the other in the word. -/
theorem LeftRootInversion.simple_bond_coefficients_eq
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (β : ι) (hβ : P.root β ∈
      leftRootInversions b (simpleWeylWord b l))
    (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -1)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hpβ : simpleRootCoeffInt b β p ≠ 0)
    (hqβ : simpleRootCoeffInt b β q ≠ 0) :
    simpleRootCoeffInt b β p = simpleRootCoeffInt b β q := by
  have hpqne : p ≠ q := by
    intro he
    subst q
    rw [RootPairing.pairingIn_same] at hpq
    omega
  have hp : p ∈ l :=
    LeftRootInversion.support_letter_mem_word b l hl β hβ p hpβ
  have hq : q ∈ l :=
    LeftRootInversion.support_letter_mem_word b l hl β hβ q hqβ
  have hidxne : l.idxOf p ≠ l.idxOf q := by
    intro he
    exact hpqne ((List.idxOf_inj hp).mp he)
  rcases lt_or_gt_of_ne hidxne with hpBefore | hqBefore
  · have hcoeff := LeftRootInversion.bond_coefficient_eq_of_word_order
      b l hl β hβ p q hpqne (by rw [hqp]; norm_num)
      hpβ hqβ hpBefore
    simpa [hqp] using hcoeff
  · have hcoeff := LeftRootInversion.bond_coefficient_eq_of_word_order
      b l hl β hβ q p hpqne.symm (by rw [hpq]; norm_num)
      hqβ hpβ hqBefore
    simpa [hpq] using hcoeff.symm

end ReductiveGroups
