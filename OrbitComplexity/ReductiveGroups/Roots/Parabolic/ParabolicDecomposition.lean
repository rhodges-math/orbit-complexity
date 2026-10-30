import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicLength

/-!
# Unique right parabolic decomposition

The projection selects the unique ordinary minimum of a right coset.
Length additivity and uniqueness are consequences of exchange.
The equivalent simple-descent criterion is proved after this construction.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Two minimal representatives in one right coset coincide. -/
theorem minimalRightParabolic_eq_of_mul (b : P.Base) (J : Set b.support)
    (d e a : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (he : IsMinimalRightParabolic b J e) (ha : a ∈ standardParabolicSubgroup b J)
    (heq : e = d * a) : e = d := by
  have hadd := RootInversionCount.mul_parabolic_of_minimal_right b J d a hd ha
  have hmin := he a⁻¹ ((standardParabolicSubgroup b J).inv_mem ha)
  rw [heq, mul_inv_cancel_right] at hmin
  have hzero : rootInversionCount b a = 0 := by omega
  have haone := (rootInversionCount_eq_zero_iff b a).mp hzero
  simpa only [haone, mul_one] using heq

/-- Both factors are unique in a right parabolic decomposition. -/
theorem rightParabolic_factorization_unique (b : P.Base) (J : Set b.support)
    (d a e c : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (he : IsMinimalRightParabolic b J e)
    (ha : a ∈ standardParabolicSubgroup b J) (hc : c ∈ standardParabolicSubgroup b J)
    (hprod : d * a = e * c) : d = e ∧ a = c := by
  have hcoset : e = d * (a * c⁻¹) := by
    calc
      e = (e * c) * c⁻¹ := by simp
      _ = (d * a) * c⁻¹ := by rw [hprod]
      _ = d * (a * c⁻¹) := mul_assoc _ _ _
  have heq := minimalRightParabolic_eq_of_mul b J d e (a * c⁻¹) hd he
    ((standardParabolicSubgroup b J).mul_mem ha ((standardParabolicSubgroup b J).inv_mem hc))
    hcoset
  exact ⟨heq.symm, mul_left_cancel (by simpa only [heq] using hprod)⟩

/-- Existence and uniqueness use the generated subgroup and
minimum length over its right coset. -/
theorem ParabolicDecomposition.existsUnique_factorization (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) :
    ∃! da : P.weylGroup × P.weylGroup,
      IsMinimalRightParabolic b J da.1 ∧ da.2 ∈ standardParabolicSubgroup b J ∧
        w = da.1 * da.2 := by
  obtain ⟨d, a, hd, ha, hw⟩ := ParabolicSubgroup.exists_rightParabolic_factorization b J w
  refine ⟨(d, a), ⟨hd, ha, hw⟩, ?_⟩
  rintro ⟨e, c⟩ ⟨he, hc, hec⟩
  obtain ⟨hde, hac⟩ := rightParabolic_factorization_unique b J d a e c hd he ha hc
    (hw.symm.trans hec)
  exact Prod.ext hde.symm hac.symm

/-- The unique right parabolic decomposition. -/
def rightParabolicDecomposition (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    P.weylGroup × P.weylGroup :=
  Classical.choose (ParabolicDecomposition.existsUnique_factorization b J w)

/-- Right projection to the minimum-length coset representative. -/
def rightParabolicRepresentative (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    P.weylGroup := (rightParabolicDecomposition b J w).1

/-- The parabolic factor on the right. -/
def rightParabolicFactor (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    P.weylGroup := (rightParabolicDecomposition b J w).2

/-- The equality is

```lean
IsMinimalRightParabolic b J (rightParabolicRepresentative b J w) ∧
      rightParabolicFactor b J w ∈ standardParabolicSubgroup b J ∧
      w = rightParabolicRepresentative b J w * rightParabolicFactor b J w
```
-/
theorem rightParabolicDecomposition_spec (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    IsMinimalRightParabolic b J (rightParabolicRepresentative b J w) ∧
      rightParabolicFactor b J w ∈ standardParabolicSubgroup b J ∧
      w = rightParabolicRepresentative b J w * rightParabolicFactor b J w :=
  (Classical.choose_spec (ParabolicDecomposition.existsUnique_factorization b J w)).1

/-- For these parameters,

```lean
IsMinimalRightParabolic b J (rightParabolicRepresentative b J w)
```
-/
theorem rightParabolicRepresentative_minimal (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : IsMinimalRightParabolic b J (rightParabolicRepresentative b J w) :=
  (rightParabolicDecomposition_spec b J w).1

/-- For these parameters,

```lean
rightParabolicFactor b J w ∈ standardParabolicSubgroup b J
```
-/
theorem rightParabolicFactor_mem (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    rightParabolicFactor b J w ∈ standardParabolicSubgroup b J :=
  (rightParabolicDecomposition_spec b J w).2.1

/-- The equality is

```lean
w = rightParabolicRepresentative b J w * rightParabolicFactor b J w
```
-/
theorem rightParabolic_factorization (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    w = rightParabolicRepresentative b J w * rightParabolicFactor b J w :=
  (rightParabolicDecomposition_spec b J w).2.2

/-- The equality is

```lean
rootInversionCount b w =
      rootInversionCount b (rightParabolicRepresentative b J w) +
        rootInversionCount b (rightParabolicFactor b J w)
```
-/
theorem RootInversionCount.rightParabolic_decomposition (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : rootInversionCount b w =
      rootInversionCount b (rightParabolicRepresentative b J w) +
        rootInversionCount b (rightParabolicFactor b J w) := by
  conv_lhs => rw [rightParabolic_factorization b J w]
  exact RootInversionCount.mul_parabolic_of_minimal_right b J _ _
    (rightParabolicRepresentative_minimal b J w) (rightParabolicFactor_mem b J w)

/-- Any independently ordinary minimum and subgroup factor are
the canonical factors. -/
theorem rightParabolic_factors_eq (b : P.Base) (J : Set b.support)
    (w d a : P.weylGroup) (hd : IsMinimalRightParabolic b J d)
    (ha : a ∈ standardParabolicSubgroup b J) (hw : w = d * a) :
    rightParabolicRepresentative b J w = d ∧ rightParabolicFactor b J w = a :=
  rightParabolic_factorization_unique b J _ _ d a
    (rightParabolicRepresentative_minimal b J w) hd (rightParabolicFactor_mem b J w) ha
    ((rightParabolic_factorization b J w).symm.trans hw)

/-- The equality is

```lean
rightParabolicRepresentative b J d = d
```
-/
@[simp] theorem rightParabolicRepresentative_of_minimal (b : P.Base) (J : Set b.support)
    (d : P.weylGroup) (hd : IsMinimalRightParabolic b J d) :
    rightParabolicRepresentative b J d = d :=
  (rightParabolic_factors_eq b J d d 1 hd (standardParabolicSubgroup b J).one_mem
    (mul_one d).symm).1

/-- The equality is

```lean
rightParabolicRepresentative b J (w * a) = rightParabolicRepresentative b J w
```
-/
@[simp] theorem rightParabolicRepresentative_mul (b : P.Base) (J : Set b.support)
    (w a : P.weylGroup) (ha : a ∈ standardParabolicSubgroup b J) :
    rightParabolicRepresentative b J (w * a) = rightParabolicRepresentative b J w := by
  exact (rightParabolic_factors_eq b J (w * a) (rightParabolicRepresentative b J w)
    (rightParabolicFactor b J w * a) (rightParabolicRepresentative_minimal b J w)
    ((standardParabolicSubgroup b J).mul_mem (rightParabolicFactor_mem b J w) ha)
    (by rw [← mul_assoc, ← rightParabolic_factorization b J w])).1

/-- Global minimum length in the right coset is equivalent to absence of
right descents in the prescribed simple generators. -/
theorem isMinimalRightParabolic_iff_simple (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : IsMinimalRightParabolic b J w ↔
      ∀ i ∈ J, rootInversionCount b w ≤
        rootInversionCount b (w * RootPairing.weylGroup.ofIdx P i) := by
  constructor
  · intro hw i hi
    exact hw _ (simple_mem_standardParabolicSubgroup b J i hi)
  · intro hn
    obtain ⟨d, a, hd, ha, hw⟩ := ParabolicSubgroup.exists_rightParabolic_factorization b J w
    obtain ⟨l, hl, hprod, hlen⟩ := exists_reduced_standardParabolic_word b J a ha
    rcases List.eq_nil_or_concat' l with rfl | ⟨k, i, rfl⟩
    · have haone : a = 1 := by simpa only [simpleWeylWord] using hprod.symm
      simpa only [hw, haone, mul_one] using hd
    · have hi : i ∈ J := hl i (by simp)
      have hk : ∀ j ∈ k, j ∈ J := fun j hj => hl j (List.mem_append_left _ hj)
      have hred : rootInversionCount b (simpleWeylWord b (k ++ [i])) =
          (k ++ [i]).length := by rw [hprod, hlen]
      have hkred := RootInversionCount.prefix_of_reduced_append_singleton b k i hred
      have hcancel : w * RootPairing.weylGroup.ofIdx P i = d * simpleWeylWord b k := by
        rw [hw, ← hprod, simpleWeylWord_append]
        simp [simpleWeylWord, mul_assoc]
      have hlow := RootInversionCount.mul_parabolic_word_of_minimal_right b J d hd k hk hkred
      have hhigh := RootInversionCount.mul_parabolic_of_minimal_right b J d a hd ha
      have hnd := hn i hi
      rw [hcancel, hlow, hw, hhigh, ← hlen] at hnd
      simp only [List.length_append, List.length_singleton] at hnd
      omega

end ReductiveGroups
