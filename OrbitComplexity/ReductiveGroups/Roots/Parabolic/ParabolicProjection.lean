import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicDecomposition
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionProduct

/-!
# Parabolic projections and inversion

Left projection is obtained by applying the proved right projection to the
inverse, exactly . Both minimality predicates mean
ordinary minimum length in the corresponding coset. Bruhat monotonicity of
both projections is `Roots/ParabolicBruhat.lean`.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The ordinary right-coset minimum criterion in root signs. -/
theorem isMinimalRightParabolic_iff_isPos (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : IsMinimalRightParabolic b J w ↔
      ∀ i ∈ J, b.IsPos (P.weylGroupToPerm w i) := by
  rw [isMinimalRightParabolic_iff_simple]
  constructor
  · intro hw i hi
    by_contra hpos
    have hneg := rootInversionCount_mul_simple_of_neg b w i
      ((root_height_neg_iff_not_isPos b _).mpr hpos)
    have hle := hw i hi
    omega
  · intro hw i hi
    rw [rootInversionCount_mul_simple_of_pos b w i (hw i hi)]
    omega

/-- The equality is

```lean
rightParabolicRepresentative b J (rightParabolicRepresentative b J w) =
      rightParabolicRepresentative b J w
```
-/
@[simp] theorem rightParabolicRepresentative_idempotent (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : rightParabolicRepresentative b J (rightParabolicRepresentative b J w) =
      rightParabolicRepresentative b J w :=
  rightParabolicRepresentative_of_minimal b J _ (rightParabolicRepresentative_minimal b J w)

/-- A reduced expression adapted to the right factorization, with
a suffix consisting only of parabolic letters. -/
theorem exists_reduced_rightParabolic_word (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : ∃ l k : List b.support,
      (∀ i ∈ k, i ∈ J) ∧
      simpleWeylWord b l = rightParabolicRepresentative b J w ∧
      simpleWeylWord b k = rightParabolicFactor b J w ∧
      simpleWeylWord b (l ++ k) = w ∧
      rootInversionCount b w = (l ++ k).length := by
  obtain ⟨l, hl, hllen⟩ := InversionLength.exists_of_inversionCount_length b
    (rightParabolicRepresentative b J w)
  obtain ⟨k, hk, hprod, hklen⟩ := exists_reduced_standardParabolic_word b J
    (rightParabolicFactor b J w) (rightParabolicFactor_mem b J w)
  refine ⟨l, k, hk, hl, hprod, ?_, ?_⟩
  · rw [simpleWeylWord_append, hl, hprod, ← rightParabolic_factorization b J w]
  · rw [List.length_append, hllen, hklen, RootInversionCount.rightParabolic_decomposition]

/-- Ordinary minimum-length representatives of left parabolic cosets. -/
def IsMinimalLeftParabolic (b : P.Base) (J : Set b.support) (d : P.weylGroup) : Prop :=
  ∀ a ∈ standardParabolicSubgroup b J, rootInversionCount b d ≤ rootInversionCount b (a * d)

/-- Inversion interchanges the ordinary left and right minimum conditions. -/
theorem isMinimalLeftParabolic_iff_inv (b : P.Base) (J : Set b.support)
    (d : P.weylGroup) : IsMinimalLeftParabolic b J d ↔ IsMinimalRightParabolic b J d⁻¹ := by
  constructor
  · intro hd a ha
    have h := hd a⁻¹ ((standardParabolicSubgroup b J).inv_mem ha)
    have heq : d⁻¹ * a = (a⁻¹ * d)⁻¹ := by simp
    simpa only [heq, rootInversionCount_inv] using h
  · intro hd a ha
    have h := hd a⁻¹ ((standardParabolicSubgroup b J).inv_mem ha)
    have heq : d⁻¹ * a⁻¹ = (a * d)⁻¹ := by simp
    simpa only [heq, rootInversionCount_inv] using h

/-- Left projection constructed from right projection by inversion. -/
def leftParabolicRepresentative (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    P.weylGroup := (rightParabolicRepresentative b J w⁻¹)⁻¹

/-- The parabolic factor on the left. -/
def leftParabolicFactor (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    P.weylGroup := (rightParabolicFactor b J w⁻¹)⁻¹

/-- For these parameters,

```lean
IsMinimalLeftParabolic b J (leftParabolicRepresentative b J w)
```
-/
theorem leftParabolicRepresentative_minimal (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : IsMinimalLeftParabolic b J (leftParabolicRepresentative b J w) := by
  rw [isMinimalLeftParabolic_iff_inv]
  simpa only [leftParabolicRepresentative, inv_inv] using
    rightParabolicRepresentative_minimal b J w⁻¹

/-- For these parameters,

```lean
leftParabolicFactor b J w ∈ standardParabolicSubgroup b J
```
-/
theorem leftParabolicFactor_mem (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    leftParabolicFactor b J w ∈ standardParabolicSubgroup b J :=
  (standardParabolicSubgroup b J).inv_mem (rightParabolicFactor_mem b J w⁻¹)

/-- The equality is

```lean
w = leftParabolicFactor b J w * leftParabolicRepresentative b J w
```
-/
theorem leftParabolic_factorization (b : P.Base) (J : Set b.support) (w : P.weylGroup) :
    w = leftParabolicFactor b J w * leftParabolicRepresentative b J w := by
  have h := congrArg Inv.inv (rightParabolic_factorization b J w⁻¹)
  simpa only [leftParabolicFactor, leftParabolicRepresentative, inv_inv, mul_inv_rev] using h

/-- Additivity for every ordinary minimum-length left representative. -/
theorem RootInversionCount.mul_parabolic_of_minimal_left (b : P.Base)
    (J : Set b.support) (a d : P.weylGroup) (hd : IsMinimalLeftParabolic b J d)
    (ha : a ∈ standardParabolicSubgroup b J) :
    rootInversionCount b (a * d) = rootInversionCount b a + rootInversionCount b d := by
  have h := RootInversionCount.mul_parabolic_of_minimal_right b J d⁻¹ a⁻¹
    ((isMinimalLeftParabolic_iff_inv b J d).mp hd) ((standardParabolicSubgroup b J).inv_mem ha)
  have heq : d⁻¹ * a⁻¹ = (a * d)⁻¹ := by simp
  simpa only [heq, rootInversionCount_inv, Nat.add_comm] using h

/-- The equality is

```lean
rootInversionCount b w =
      rootInversionCount b (leftParabolicFactor b J w) +
        rootInversionCount b (leftParabolicRepresentative b J w)
```
-/
theorem RootInversionCount.leftParabolic_decomposition (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : rootInversionCount b w =
      rootInversionCount b (leftParabolicFactor b J w) +
        rootInversionCount b (leftParabolicRepresentative b J w) := by
  conv_lhs => rw [leftParabolic_factorization b J w]
  exact RootInversionCount.mul_parabolic_of_minimal_left b J _ _
    (leftParabolicRepresentative_minimal b J w) (leftParabolicFactor_mem b J w)

/-- Uniqueness on the left follows from uniqueness on the right by inversion. -/
theorem leftParabolic_factors_eq (b : P.Base) (J : Set b.support)
    (w a d : P.weylGroup) (hd : IsMinimalLeftParabolic b J d)
    (ha : a ∈ standardParabolicSubgroup b J) (hw : w = a * d) :
    leftParabolicFactor b J w = a ∧ leftParabolicRepresentative b J w = d := by
  have hi : w⁻¹ = d⁻¹ * a⁻¹ := by rw [hw, mul_inv_rev]
  obtain ⟨hd', ha'⟩ := rightParabolic_factors_eq b J w⁻¹ d⁻¹ a⁻¹
    ((isMinimalLeftParabolic_iff_inv b J d).mp hd)
    ((standardParabolicSubgroup b J).inv_mem ha) hi
  exact ⟨by simp only [leftParabolicFactor, ha', inv_inv],
    by simp only [leftParabolicRepresentative, hd', inv_inv]⟩

/-- The equality is

```lean
rightParabolicRepresentative b J w⁻¹ =
      (leftParabolicRepresentative b J w)⁻¹
```
-/
@[simp] theorem rightParabolicRepresentative_inv (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : rightParabolicRepresentative b J w⁻¹ =
      (leftParabolicRepresentative b J w)⁻¹ := by simp [leftParabolicRepresentative]

/-- The equality is

```lean
leftParabolicRepresentative b J w⁻¹ =
      (rightParabolicRepresentative b J w)⁻¹
```
-/
@[simp] theorem leftParabolicRepresentative_inv (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : leftParabolicRepresentative b J w⁻¹ =
      (rightParabolicRepresentative b J w)⁻¹ := by simp [leftParabolicRepresentative]

/-- The left minimum condition in the precise inverse-root-sign convention. -/
theorem isMinimalLeftParabolic_iff_isPos_inv (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : IsMinimalLeftParabolic b J w ↔
      ∀ i ∈ J, b.IsPos (P.weylGroupToPerm w⁻¹ i) := by
  rw [isMinimalLeftParabolic_iff_inv, isMinimalRightParabolic_iff_isPos]

/-- Left inversions split along the proved left parabolic decomposition. -/
theorem LeftRootInversions.leftParabolic_decomposition (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) : leftRootInversions b w =
      leftRootInversions b (leftParabolicFactor b J w) ∪
        (fun β : M => leftParabolicFactor b J w • β) ''
          leftRootInversions b (leftParabolicRepresentative b J w) := by
  have h := leftRootInversions_mul_of_count_add b
    (leftParabolicFactor b J w) (leftParabolicRepresentative b J w)
    (RootInversionCount.mul_parabolic_of_minimal_left b J _ _
      (leftParabolicRepresentative_minimal b J w) (leftParabolicFactor_mem b J w))
  simpa only [← leftParabolic_factorization b J w] using h

/-- The transported second inversion set in the left factorization is positive. -/
theorem leftParabolic_image_inversions_positive (b : P.Base) (J : Set b.support)
    (w : P.weylGroup) :
    (fun β : M => leftParabolicFactor b J w • β) ''
      leftRootInversions b (leftParabolicRepresentative b J w) ⊆ P.root '' {i | b.IsPos i} :=
  InversionProduct.inversions_subset_positive_of_count_add b _ _
    (RootInversionCount.mul_parabolic_of_minimal_left b J _ _
      (leftParabolicRepresentative_minimal b J w) (leftParabolicFactor_mem b J w))

end ReductiveGroups
