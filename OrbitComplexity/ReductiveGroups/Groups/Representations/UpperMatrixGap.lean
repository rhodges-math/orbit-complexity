import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Upper Matrix Gap

The upper-diagonal filtration of square matrices. Products add gaps;
the additive commutator of upper triangular matrices has positive gap. -/

namespace ReductiveGroups
variable {R : Type*} [CommRing R] {n : ℕ}

/-- All entries less than `d` places above the diagonal vanish. -/
def matrixUpperGap (d : ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val < i.val + d → A i j = 0

/-- For these parameters,

```lean
matrixUpperGap d A
```
-/
theorem matrixUpperGap_mono {d e : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (h : matrixUpperGap e A) (hde : d ≤ e) : matrixUpperGap d A := by
  intro i j hij
  exact h i j (by omega)

/-- For these parameters,

```lean
matrixUpperGap d (A - B)
```
-/
theorem matrixUpperGap_sub {d : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap d A) (hB : matrixUpperGap d B) : matrixUpperGap d (A - B) := by
  intro i j hij
  simp only [Matrix.sub_apply, hA i j hij, hB i j hij, sub_self]

/-- For these parameters,

```lean
matrixUpperGap (d + e) (A * B)
```
-/
theorem matrixUpperGap_mul {d e : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap d A) (hB : matrixUpperGap e B) :
    matrixUpperGap (d + e) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val < i.val + d
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]

/-- The equality is

```lean
(A * B) i i = A i i * B i i
```
-/
theorem upperMatrix_mul_diag {A B : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hB : matrixUpperGap 0 B) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    by_cases hk : k.val < i.val
    · rw [hA i k (by omega), zero_mul]
    · have hik : i.val < k.val := by
        have : k.val ≠ i.val := fun h => hki (Fin.ext h)
        omega
      rw [hB k i (by omega), mul_zero]
  · simp

/-- For these parameters,

```lean
matrixUpperGap 1 (A * B - B * A)
```
-/
theorem matrixUpperGap_additive_commutator {A B : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hB : matrixUpperGap 0 B) :
    matrixUpperGap 1 (A * B - B * A) := by
  intro i j hij
  by_cases hji : j = i
  · subst j
    simp only [Matrix.sub_apply, upperMatrix_mul_diag hA hB,
      upperMatrix_mul_diag hB hA, mul_comm (A i i) (B i i), sub_self]
  · have hj : j.val < i.val := by
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
    exact matrixUpperGap_sub (matrixUpperGap_mul hA hB)
      (matrixUpperGap_mul hB hA) i j (by omega)

/-- The equality is

```lean
A = 0
```
-/
theorem matrixUpperGap_eq_zero {d : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (h : matrixUpperGap d A) (hnd : n ≤ d) : A = 0 := by
  ext i j
  exact h i j (by have := j.isLt; omega)

end ReductiveGroups
