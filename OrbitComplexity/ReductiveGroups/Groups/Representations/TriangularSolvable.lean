import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedWordClosure
import Mathlib.Tactic.NoncommRing

/-!
# Triangular Solvable

A group with a faithful upper triangular matrix representation is
solvable. The proof works over a commutative ring, uniformly in matrix size. -/

namespace ReductiveGroups
open scoped commutatorElement

variable {R : Type*} [CommRing R] {n : ℕ}

private theorem matrixUnit_commutator_sub_one
    (a b : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑⁅a, b⁆ : Matrix (Fin n) (Fin n) R) - 1 =
      ((a : Matrix (Fin n) (Fin n) R) * (b : Matrix (Fin n) (Fin n) R) -
        (b : Matrix (Fin n) (Fin n) R) * (a : Matrix (Fin n) (Fin n) R)) *
          (↑a⁻¹ : Matrix (Fin n) (Fin n) R) *
            (↑b⁻¹ : Matrix (Fin n) (Fin n) R) := by
  have hcancel : (b : Matrix (Fin n) (Fin n) R) *
      (a : Matrix (Fin n) (Fin n) R) * (↑a⁻¹ : Matrix (Fin n) (Fin n) R) *
        (↑b⁻¹ : Matrix (Fin n) (Fin n) R) = 1 := by
    simp only [mul_assoc, Units.mul_inv, mul_one]
  simp only [commutatorElement_def, Units.val_mul]
  rw [← hcancel]
  noncomm_ring

/-- For these parameters,

```lean
matrixUpperGap 1 ((↑⁅a, b⁆ : Matrix (Fin n) (Fin n) R) - 1)
```
-/
theorem matrixUnit_commutator_positive_gap
    (a b : (Matrix (Fin n) (Fin n) R)ˣ)
    (ha : matrixUpperGap 0 (a : Matrix (Fin n) (Fin n) R))
    (hb : matrixUpperGap 0 (b : Matrix (Fin n) (Fin n) R))
    (hai : matrixUpperGap 0 (↑a⁻¹ : Matrix (Fin n) (Fin n) R))
    (hbi : matrixUpperGap 0 (↑b⁻¹ : Matrix (Fin n) (Fin n) R)) :
    matrixUpperGap 1 ((↑⁅a, b⁆ : Matrix (Fin n) (Fin n) R) - 1) := by
  rw [matrixUnit_commutator_sub_one]
  exact matrixUpperGap_mul
    (matrixUpperGap_mul (matrixUpperGap_additive_commutator ha hb) hai) hbi

/-- For these parameters,

```lean
matrixUpperGap (d + d) ((↑⁅a, b⁆ : Matrix (Fin n) (Fin n) R) - 1)
```
-/
theorem matrixUnit_commutator_double_gap
    (a b : (Matrix (Fin n) (Fin n) R)ˣ) (d : ℕ)
    (ha : matrixUpperGap d ((a : Matrix (Fin n) (Fin n) R) - 1))
    (hb : matrixUpperGap d ((b : Matrix (Fin n) (Fin n) R) - 1))
    (hai : matrixUpperGap 0 (↑a⁻¹ : Matrix (Fin n) (Fin n) R))
    (hbi : matrixUpperGap 0 (↑b⁻¹ : Matrix (Fin n) (Fin n) R)) :
    matrixUpperGap (d + d) ((↑⁅a, b⁆ : Matrix (Fin n) (Fin n) R) - 1) := by
  rw [matrixUnit_commutator_sub_one]
  have heq : (a : Matrix (Fin n) (Fin n) R) * (b : Matrix (Fin n) (Fin n) R) -
      (b : Matrix (Fin n) (Fin n) R) * (a : Matrix (Fin n) (Fin n) R) =
      (↑a - 1) * (↑b - 1) - (↑b - 1) * (↑a - 1) := by noncomm_ring
  rw [heq]
  simpa only [Nat.add_zero] using matrixUpperGap_mul (matrixUpperGap_mul
    (matrixUpperGap_sub (matrixUpperGap_mul ha hb) (matrixUpperGap_mul hb ha)) hai) hbi

variable {G : Type*} [Group G]

/-- For these parameters,

```lean
matrixUpperGap (m + 1)
      ((ρ (derivedGroupWord (m + 1) x) : Matrix (Fin n) (Fin n) R) - 1)
```
-/
theorem upperTriangular_derivedWord_gap
    (ρ : G →* (Matrix (Fin n) (Fin n) R)ˣ)
    (hρ : ∀ g, matrixUpperGap 0 (ρ g : Matrix (Fin n) (Fin n) R))
    (m : ℕ) (x : DerivedWordIndex (m + 1) → G) :
    matrixUpperGap (m + 1)
      ((ρ (derivedGroupWord (m + 1) x) : Matrix (Fin n) (Fin n) R) - 1) := by
  induction m with
  | zero =>
      rw [derivedGroupWord_succ, map_commutatorElement]
      apply matrixUnit_commutator_positive_gap _ _ (hρ _) (hρ _)
      · simpa only [map_inv] using hρ ((derivedGroupWord 0 (fun i => x (false, i)))⁻¹)
      · simpa only [map_inv] using hρ ((derivedGroupWord 0 (fun i => x (true, i)))⁻¹)
  | succ m ih =>
      rw [derivedGroupWord_succ, map_commutatorElement]
      apply matrixUpperGap_mono (d := m + 1 + 1) (e := (m + 1) + (m + 1)) _ (by omega)
      apply matrixUnit_commutator_double_gap _ _ (m + 1) (ih _) (ih _)
      · simpa only [map_inv] using hρ ((derivedGroupWord (m + 1) (fun i => x (false, i)))⁻¹)
      · simpa only [map_inv] using hρ ((derivedGroupWord (m + 1) (fun i => x (true, i)))⁻¹)

/-- For these parameters,

```lean
Group.IsSolvable G
```
-/
theorem isSolvable_of_faithful_upperTriangular
    (ρ : G →* (Matrix (Fin n) (Fin n) R)ˣ) (hρinj : Function.Injective ρ)
    (hρ : ∀ g, matrixUpperGap 0 (ρ g : Matrix (Fin n) (Fin n) R)) :
    Group.IsSolvable G := by
  apply isSolvable_of_derivedGroupWord_identity (n + 1)
  intro x
  apply hρinj
  rw [map_one]
  apply Units.ext
  apply sub_eq_zero.mp
  exact matrixUpperGap_eq_zero (upperTriangular_derivedWord_gap ρ hρ n x) (by omega)

end ReductiveGroups
