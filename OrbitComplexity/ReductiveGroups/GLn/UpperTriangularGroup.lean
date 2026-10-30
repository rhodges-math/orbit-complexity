import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The group of invertible upper-triangular matrices is solvable

For a commutative ring `F`, the invertible upper-triangular `n × n` matrices form a subgroup of
`GL_n(F)`. It is solvable: let `U_d` be the subgroup of upper-triangular matrices `g` such that
`g - 1` vanishes on the diagonals `0, …, d - 1`. The commutator of two upper-triangular matrices
lies in `U_1`, and the commutator of two elements of `U_d` lies in `U_{d+1}` (indeed in `U_{2d}`
for `d ≥ 1`), because `ghg⁻¹h⁻¹ - 1 = (gh - hg)g⁻¹h⁻¹` and `gh - hg = [g - 1, h - 1]`. Since
`U_n` is trivial, the derived series terminates after `n` steps.

## Main declarations

* `ReductiveGroups.GLn.upperTriangularGroup`: the invertible upper-triangular matrices.
* `ReductiveGroups.GLn.isSolvable_upperTriangularGroup`: this group is solvable.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.1.
* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), §6.1.
-/

namespace ReductiveGroups.GLn

open scoped commutatorElement

section UpperTriangular

variable (F : Type*) [CommRing F] (n : ℕ)

/-- The subgroup of invertible upper-triangular matrices. -/
def upperTriangularGroup : Subgroup (GL (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular}
  mul_mem' := by
    intro a b ha hb
    exact Matrix.BlockTriangular.mul ha hb
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := by
    intro g hg
    change (↑g⁻¹ : Matrix (Fin n) (Fin n) F).IsUpperTriangular
    rw [Matrix.coe_units_inv]
    let _ : Invertible (g : Matrix (Fin n) (Fin n) F) := g.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

variable {F n} in
/-- The equivalence is

```lean
g ∈ upperTriangularGroup F n ↔ (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular
```
-/
theorem mem_upperTriangularGroup_iff (g : GL (Fin n) F) :
    g ∈ upperTriangularGroup F n ↔ (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular :=
  Iff.rfl

variable {F n}

/-- The equivalence is

```lean
matrixUpperGap 0 A ↔ A.IsUpperTriangular
```
-/
theorem matrixUpperGap_zero_iff (A : Matrix (Fin n) (Fin n) F) :
    matrixUpperGap 0 A ↔ A.IsUpperTriangular := by
  constructor
  · intro h i j hij
    exact h i j (by simpa using hij)
  · intro h i j hij
    exact h (show j < i by simpa using hij)

/-- For these parameters,

```lean
matrixUpperGap d (A + C)
```
-/
theorem matrixUpperGap_add' {d : ℕ} {A C : Matrix (Fin n) (Fin n) F}
    (hA : matrixUpperGap d A) (hC : matrixUpperGap d C) : matrixUpperGap d (A + C) := by
  intro i j hij
  rw [Matrix.add_apply, hA i j hij, hC i j hij, add_zero]

/-- For these parameters,

```lean
matrixUpperGap d (0 : Matrix (Fin n) (Fin n) F)
```
-/
theorem matrixUpperGap_zero' {d : ℕ} : matrixUpperGap d (0 : Matrix (Fin n) (Fin n) F) := by
  intro i j _
  rfl

/-- For these parameters,

```lean
matrixUpperGap d (-A)
```
-/
theorem matrixUpperGap_neg {d : ℕ} {A : Matrix (Fin n) (Fin n) F}
    (h : matrixUpperGap d A) : matrixUpperGap d (-A) := by
  intro i j hij
  rw [Matrix.neg_apply, h i j hij, neg_zero]

variable (F n) in
/-- The subgroup `U_d` of upper-triangular matrices congruent to the identity on the first `d`
diagonals. -/
def gapSubgroup (d : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular ∧
    matrixUpperGap d ((g : Matrix (Fin n) (Fin n) F) - 1)}
  mul_mem' := by
    intro a b ha hb
    refine ⟨Matrix.BlockTriangular.mul ha.1 hb.1, ?_⟩
    have hsplit : ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        ((a : Matrix (Fin n) (Fin n) F) - 1) * ((b : Matrix (Fin n) (Fin n) F) - 1) +
          ((a : Matrix (Fin n) (Fin n) F) - 1) + ((b : Matrix (Fin n) (Fin n) F) - 1) := by
      rw [Units.val_mul]
      noncomm_ring
    rw [hsplit]
    exact matrixUpperGap_add' (matrixUpperGap_add'
      (matrixUpperGap_mono (matrixUpperGap_mul ha.2 hb.2) (Nat.le_add_right d d)) ha.2) hb.2
  one_mem' := by
    refine ⟨Matrix.blockTriangular_one, ?_⟩
    rw [Units.val_one, sub_self]
    exact matrixUpperGap_zero'
  inv_mem' := by
    intro g hg
    have hinv : (upperTriangularGroup F n).carrier g⁻¹ :=
      (upperTriangularGroup F n).inv_mem hg.1
    refine ⟨hinv, ?_⟩
    have hsplit : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        (g⁻¹ : GL (Fin n) F) * (-((g : Matrix (Fin n) (Fin n) F) - 1)) := by
      rw [mul_neg, mul_sub, mul_one, Units.inv_mul]
      noncomm_ring
    rw [hsplit]
    have h0 : matrixUpperGap 0 ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      (matrixUpperGap_zero_iff _).mpr hinv
    simpa using matrixUpperGap_mul h0 (matrixUpperGap_neg hg.2)

/-- The inclusion is

```lean
upperTriangularGroup F n ≤ gapSubgroup F n 0
```
-/
theorem upperTriangularGroup_le_gapSubgroup_zero :
    upperTriangularGroup F n ≤ gapSubgroup F n 0 := by
  intro g hg
  refine ⟨hg, ?_⟩
  have hone : matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) F) :=
    (matrixUpperGap_zero_iff _).mpr Matrix.blockTriangular_one
  exact matrixUpperGap_sub ((matrixUpperGap_zero_iff _).mpr hg) hone

/-- Commutators of elements of `U_d` lie in `U_{d+1}`. -/
theorem commutator_mem_gapSubgroup_succ {d : ℕ} {g h : GL (Fin n) F}
    (hg : g ∈ gapSubgroup F n d) (hh : h ∈ gapSubgroup F n d) :
    ⁅g, h⁆ ∈ gapSubgroup F n (d + 1) := by
  have hcomm : ⁅g, h⁆ ∈ upperTriangularGroup F n := by
    rw [commutatorElement_def]
    exact (upperTriangularGroup F n).mul_mem ((upperTriangularGroup F n).mul_mem
      ((upperTriangularGroup F n).mul_mem hg.1 hh.1) ((upperTriangularGroup F n).inv_mem hg.1))
      ((upperTriangularGroup F n).inv_mem hh.1)
  refine ⟨hcomm, ?_⟩
  set x : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1
  set y : Matrix (Fin n) (Fin n) F := (h : Matrix (Fin n) (Fin n) F) - 1
  have hsplit : ((⁅g, h⁆ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      (x * y - y * x) *
        (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
    have hgi : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = 1 := Units.mul_inv g
    have hhi : (h : Matrix (Fin n) (Fin n) F) * ((h⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = 1 := Units.mul_inv h
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
    simp only [x, y]
    have key : ((g : Matrix (Fin n) (Fin n) F) - 1) * ((h : Matrix (Fin n) (Fin n) F) - 1) -
        ((h : Matrix (Fin n) (Fin n) F) - 1) * ((g : Matrix (Fin n) (Fin n) F) - 1) =
        (g : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) -
          (h : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) := by
      noncomm_ring
    rw [key, sub_mul]
    have h2 : (h : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
        (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g : Matrix (Fin n) (Fin n) F), hgi,
        Matrix.one_mul, hhi]
    rw [h2]
    simp only [Matrix.mul_assoc]
  rw [hsplit]
  have hxy : matrixUpperGap (d + 1) (x * y - y * x) := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exact matrixUpperGap_additive_commutator hg.2 hh.2
    · exact matrixUpperGap_mono
        (matrixUpperGap_sub (matrixUpperGap_mul hg.2 hh.2) (matrixUpperGap_mul hh.2 hg.2))
        (by omega)
  have hinv : matrixUpperGap 0 (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    (matrixUpperGap_zero_iff _).mpr
      ((upperTriangularGroup F n).mul_mem ((upperTriangularGroup F n).inv_mem hg.1)
        ((upperTriangularGroup F n).inv_mem hh.1))
  simpa using matrixUpperGap_mul hxy hinv

/-- The `k`-th derived subgroup of the upper-triangular group lies in `U_k`. -/
theorem derivedSeries_le_gapSubgroup (k : ℕ) :
    ∀ x ∈ derivedSeries (upperTriangularGroup F n) k,
      (x : GL (Fin n) F) ∈ gapSubgroup F n k := by
  induction k with
  | zero =>
      intro x _
      exact upperTriangularGroup_le_gapSubgroup_zero x.2
  | succ k ih =>
      intro x hx
      rw [derivedSeries_succ] at hx
      have hle : ⁅derivedSeries (upperTriangularGroup F n) k,
          derivedSeries (upperTriangularGroup F n) k⁆ ≤
          (gapSubgroup F n (k + 1)).comap (upperTriangularGroup F n).subtype := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_comap, map_commutatorElement]
        exact commutator_mem_gapSubgroup_succ (ih a ha) (ih b hb)
      exact hle hx

variable (F n) in
/-- **The invertible upper-triangular matrices form a solvable group.** -/
theorem isSolvable_upperTriangularGroup : Group.IsSolvable (upperTriangularGroup F n) := by
  refine ⟨⟨n, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  have h := derivedSeries_le_gapSubgroup n x hx
  have hzero : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 = 0 :=
    matrixUpperGap_eq_zero h.2 le_rfl
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  rw [sub_eq_zero] at hzero
  simpa using hzero

end UpperTriangular

end GLn
