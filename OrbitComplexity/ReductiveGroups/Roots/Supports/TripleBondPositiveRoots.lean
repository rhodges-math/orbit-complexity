import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.SupportedRootReflectionWord
import OrbitComplexity.ReductiveGroups.Roots.Supports.BooleanTripleBondShape

/-!
# Triple Bond Positive Roots

The six positive roots on a triple bond. The proof uses the
proved support-restricted reflection generation, and checks the finite
coordinate orbit under the two simple reflections. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq
open scoped BigOperators

private def tripleBondOrbitCoordinates (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨
  (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨
  (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) ∨
  (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = -1) ∨
  (x = -1 ∧ y = -1) ∨ (x = -1 ∧ y = -2) ∨
  (x = -1 ∧ y = -3) ∨ (x = -2 ∧ y = -3)

private theorem tripleBondOrbitCoordinates_reflect_first {x y : ℤ}
    (h : tripleBondOrbitCoordinates x y) : tripleBondOrbitCoordinates (y - x) y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [tripleBondOrbitCoordinates]

private theorem TripleBondOrbitCoordinates.reflect_second {x y : ℤ}
    (h : tripleBondOrbitCoordinates x y) : tripleBondOrbitCoordinates x (3 * x - y) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [tripleBondOrbitCoordinates]

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [IsDomain R] [Finite ι] [P.IsReduced] in
/-- The equality is

```lean
P.pairingIn ℤ β (p : ι) = 2 * simpleRootCoeffInt b β p - simpleRootCoeffInt b β q ∧
    P.pairingIn ℤ β (q : ι) = -3 * simpleRootCoeffInt b β p + 2 * simpleRootCoeffInt b β q
```
-/
theorem tripleBond_supported_pairings (b : P.Base) (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (β : ι) (hsupport : simpleRootSupportInt b β ⊆ ({p, q} : Set b.support)) :
    P.pairingIn ℤ β (p : ι) = 2 * simpleRootCoeffInt b β p - simpleRootCoeffInt b β q ∧
    P.pairingIn ℤ β (q : ι) = -3 * simpleRootCoeffInt b β p + 2 * simpleRootCoeffInt b β q := by
  have hpqne : p ≠ q := by
    intro h
    subst q
    rw [P.pairingIn_same] at hpq
    omega
  have hsum (j : b.support) : P.pairingIn ℤ β (j : ι) =
      simpleRootCoeffInt b β p * P.pairingIn ℤ (p : ι) (j : ι) +
      simpleRootCoeffInt b β q * P.pairingIn ℤ (q : ι) (j : ι) := by
    rw [pairingIn_eq_sum_simpleRootCoeffInt b β j]
    have he : (∑ k : b.support, simpleRootCoeffInt b β k * P.pairingIn ℤ (k : ι) (j : ι)) =
        ∑ k ∈ ({p, q} : Finset b.support),
          simpleRootCoeffInt b β k * P.pairingIn ℤ (k : ι) (j : ι) := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro k _ hk
      have hz : simpleRootCoeffInt b β k = 0 := by
        by_contra hn
        have hm := hsupport hn
        exact hk (by simpa using hm)
      simp [hz]
    rw [he, Finset.sum_pair hpqne]
  constructor
  · rw [hsum p, P.pairingIn_same, hqp]
    ring
  · rw [hsum q, P.pairingIn_same, hpq]
    ring

/-- The equality is

```lean
(simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 0) ∨
    (simpleRootCoeffInt b β p = 0 ∧ simpleRootCoeffInt b β q = 1) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 1) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 2) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 3) ∨
    (simpleRootCoeffInt b β p = 2 ∧ simpleRootCoeffInt b β q = 3)
```
-/
theorem positiveRoot_tripleBond_coordinates (b : P.Base) (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (β : ι) (hβ : b.IsPos β)
    (hsupport : simpleRootSupportInt b β ⊆ ({p, q} : Set b.support)) :
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 0) ∨
    (simpleRootCoeffInt b β p = 0 ∧ simpleRootCoeffInt b β q = 1) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 1) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 2) ∨
    (simpleRootCoeffInt b β p = 1 ∧ simpleRootCoeffInt b β q = 3) ∨
    (simpleRootCoeffInt b β p = 2 ∧ simpleRootCoeffInt b β q = 3) := by
  have hpqne : p ≠ q := by
    intro h
    subst q
    rw [P.pairingIn_same] at hpq
    omega
  have horbit (word : List b.support)
      (hword : ∀ j ∈ word, j ∈ ({p, q} : Set b.support))
      (i : b.support) (hi : i ∈ ({p, q} : Set b.support)) :
      tripleBondOrbitCoordinates
        (simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) i) p)
        (simpleRootCoeffInt b (P.weylGroupToPerm (simpleWeylWord b word) i) q) := by
    induction word with
    | nil =>
      change tripleBondOrbitCoordinates (simpleRootCoeffInt b (i : ι) p)
        (simpleRootCoeffInt b (i : ι) q)
      rcases hi with rfl | rfl <;>
        simp [simpleRootCoeffInt_simple, hpqne, hpqne.symm, tripleBondOrbitCoordinates]
    | cons j word ih =>
      have ht := ih (fun k hk => hword k (List.mem_cons_of_mem _ hk))
      let δ : ι := P.weylGroupToPerm (simpleWeylWord b word) i
      have hs : simpleRootSupportInt b δ ⊆ ({p, q} : Set b.support) := by
        apply simpleWeylWord_preserves_root_support b _ word
          (fun k hk => hword k (List.mem_cons_of_mem _ hk)) (i : ι)
        rw [simpleRootSupportInt_simple_eq]
        exact Set.singleton_subset_iff.mpr hi
      have hpair := tripleBond_supported_pairings b p q hpq hqp δ hs
      change tripleBondOrbitCoordinates (simpleRootCoeffInt b δ p) (simpleRootCoeffInt b δ q) at ht
      change tripleBondOrbitCoordinates
        (simpleRootCoeffInt b (P.reflectionPerm (j : ι) δ) p)
        (simpleRootCoeffInt b (P.reflectionPerm (j : ι) δ) q)
      have hj := hword j (by simp)
      rcases hj with hjp | hjq
      · change j = p at hjp
        subst j
        rw [simpleRootCoeffInt_reflection, simpleRootCoeffInt_reflection]
        simp only [ite_true, ite_eq_right hpqne, mul_one, mul_zero, sub_zero, hpair.1]
        have he : simpleRootCoeffInt b δ p -
              (2 * simpleRootCoeffInt b δ p - simpleRootCoeffInt b δ q) =
            simpleRootCoeffInt b δ q - simpleRootCoeffInt b δ p := by ring
        rw [he]
        exact tripleBondOrbitCoordinates_reflect_first ht
      · change j = q at hjq
        subst j
        rw [simpleRootCoeffInt_reflection, simpleRootCoeffInt_reflection]
        simp only [ite_true, ite_eq_right hpqne.symm, mul_one, mul_zero, sub_zero, hpair.2]
        have he : simpleRootCoeffInt b δ q -
              (-3 * simpleRootCoeffInt b δ p + 2 * simpleRootCoeffInt b δ q) =
            3 * simpleRootCoeffInt b δ p - simpleRootCoeffInt b δ q := by ring
        rw [he]
        exact TripleBondOrbitCoordinates.reflect_second ht
  obtain ⟨word, hword, i, hi, he⟩ :=
    SupportedRootReflectionWord.positive_root_exists_simple_word b {p, q} β hβ hsupport
  have hc := horbit word hword i hi
  rw [← he] at hc
  have hp := simpleRootCoeffInt_nonneg_of_isPos b β hβ p
  have hq := simpleRootCoeffInt_nonneg_of_isPos b β hβ q
  unfold tripleBondOrbitCoordinates at hc
  omega

end ReductiveGroups
