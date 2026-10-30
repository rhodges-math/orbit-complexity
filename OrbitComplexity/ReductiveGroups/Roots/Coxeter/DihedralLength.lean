import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralWords

/-!
# Inversion lengths of rank-two alternating words

Every alternating word of length at most the product order is minimal.
A putative shorter expression reduces within the same two letters; equality
of alternating products then contradicts the exact finite order. Thus the
braid word has inversion length equal to its matrix entry.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

open CoxeterSystem

/-- The equality is

```lean
l.length % 2 = k.length % 2
```
-/
theorem simpleWeylWord_length_mod_two_eq_of_eq (b : P.Base)
    (l k : List b.support) (heq : simpleWeylWord b l = simpleWeylWord b k) :
    l.length % 2 = k.length % 2 := by
  have hl := RootInversionCount.simpleWeylWord_mod_two b l
  have hk := RootInversionCount.simpleWeylWord_mod_two b k
  rw [heq] at hl
  omega

/-- Same-ending alternating words of different shorter lengths cannot agree
before the product order. -/
theorem SimpleWeylWord.alternating_ne_shorter_same (b : P.Base) (i j : b.support)
    {n k : ℕ} (hkn : k < n) (hn : n ≤ simpleCoxeterMatrix b i j) :
    simpleWeylWord b (alternatingWord i j n) ≠
      simpleWeylWord b (alternatingWord i j k) := by
  intro heq
  have hpar := simpleWeylWord_length_mod_two_eq_of_eq b _ _ heq
  simp only [length_alternatingWord] at hpar
  have hEven : Even n ↔ Even k := by simp only [Nat.even_iff]; omega
  rw [SimpleWeylWord.alternatingWord_eq_mul_pow,
    SimpleWeylWord.alternatingWord_eq_mul_pow] at heq
  simp only [hEven] at heq
  have hp := mul_left_cancel heq
  have hm := simpleCoxeterMatrix_pos b i j
  have hexp := pow_injOn_Iio_orderOf (x :=
      RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j)
    (by change n / 2 < simpleCoxeterMatrix b i j; omega)
    (by change k / 2 < simpleCoxeterMatrix b i j; omega) hp
  omega

/-- Opposite-ending alternating words cannot agree at two lengths whose
larger is at most the product order and strictly exceeds the other. -/
theorem SimpleWeylWord.alternating_ne_shorter_swap (b : P.Base) (i j : b.support)
    {n k : ℕ} (hkn : k < n) (hn : n ≤ simpleCoxeterMatrix b i j) :
    simpleWeylWord b (alternatingWord i j n) ≠
      simpleWeylWord b (alternatingWord j i k) := by
  intro heq
  have hpar := simpleWeylWord_length_mod_two_eq_of_eq b _ _ heq
  simp only [length_alternatingWord] at hpar
  let s := RootPairing.weylGroup.ofIdx P i
  let t := RootPairing.weylGroup.ofIdx P j
  let r := s * t
  have htt : t * t = 1 := weylGroup_ofIdx_mul_self (P := P) j
  have hts : t * s = r⁻¹ := by
    dsimp [r, s, t]
    simp only [mul_inv_rev, weylGroup_simple_inv]
  have hm : orderOf r = simpleCoxeterMatrix b i j := rfl
  rw [SimpleWeylWord.alternatingWord_eq_mul_pow,
    SimpleWeylWord.alternatingWord_eq_mul_pow] at heq
  change (if Even n then 1 else t) * r ^ (n / 2) =
    (if Even k then 1 else s) * (t * s) ^ (k / 2) at heq
  by_cases hnEven : Even n
  · have hkEven : Even k := by rw [Nat.even_iff] at hnEven ⊢; omega
    simp only [hnEven, hkEven, ite_true, one_mul, hts, inv_pow] at heq
    have hp : r ^ (n / 2 + k / 2) = 1 := by
      rw [pow_add, heq, inv_mul_cancel]
    have hnmod : n % 2 = 0 := Nat.even_iff.mp hnEven
    have hkmod : k % 2 = 0 := Nat.even_iff.mp hkEven
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hm]; omega) hp
  · have hkEven : ¬ Even k := by simp only [Nat.even_iff] at hnEven ⊢; omega
    simp only [hnEven, hkEven, ite_false, hts, inv_pow] at heq
    have he : r ^ (n / 2) = (r ^ (k / 2 + 1))⁻¹ := by
      calc
        r ^ (n / 2) = t * (t * r ^ (n / 2)) := by rw [← mul_assoc, htt, one_mul]
        _ = t * (s * (r ^ (k / 2))⁻¹) := by rw [heq]
        _ = r⁻¹ * (r ^ (k / 2))⁻¹ := by rw [← mul_assoc, hts]
        _ = (r ^ (k / 2 + 1))⁻¹ := by simp only [pow_succ, mul_inv_rev]
    have hp : r ^ (n / 2 + (k / 2 + 1)) = 1 := by
      rw [pow_add, he, inv_mul_cancel]
    have hnmod : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hnEven
    have hkmod : k % 2 ≠ 0 := by simpa only [Nat.even_iff] using hkEven
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hm]; omega) hp

omit [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The equality is

```lean
k = i ∨ k = j
```
-/
theorem mem_alternatingWord_two_letters (b : P.Base) (i j : b.support) (n : ℕ)
    {k : b.support} (hk : k ∈ alternatingWord i j n) : k = i ∨ k = j := by
  induction n generalizing i j with
  | zero => simp [alternatingWord] at hk
  | succ n ih =>
    simp only [alternatingWord_succ, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at hk
    rcases hk with hk | hk
    · exact (ih j i hk).symm
    · exact Or.inr hk

/-- Every alternating word through the dihedral braid length attains
the inversion-count lower bound. -/
theorem RootInversionCount.alternatingWord_eq_length (b : P.Base) (i j : b.support)
    (n : ℕ) (hn : n ≤ simpleCoxeterMatrix b i j) :
    rootInversionCount b (simpleWeylWord b (alternatingWord i j n)) = n := by
  have hle := RootInversionCount.simpleWeylWord_le_length b (alternatingWord i j n)
  simp only [length_alternatingWord] at hle
  apply le_antisymm hle
  by_contra hnot
  have hlt : rootInversionCount b (simpleWeylWord b (alternatingWord i j n)) < n := by omega
  have he := SimpleWeylWord.two_letters_minimal_alternating b i j (alternatingWord i j n)
    (fun k hk => mem_alternatingWord_two_letters b i j n hk)
  exact he.elim (SimpleWeylWord.alternating_ne_shorter_same b i j hlt hn)
    (SimpleWeylWord.alternating_ne_shorter_swap b i j hlt hn)

/-- The rank-two braid word has inversion length equal to the
order of the product of its two simple reflections. -/
theorem rootInversionCount_braidWord (b : P.Base) (i j : b.support) :
    rootInversionCount b (simpleWeylWord b (braidWord (simpleCoxeterMatrix b) i j)) =
      simpleCoxeterMatrix b i j :=
  RootInversionCount.alternatingWord_eq_length b i j _ le_rfl

end ReductiveGroups
