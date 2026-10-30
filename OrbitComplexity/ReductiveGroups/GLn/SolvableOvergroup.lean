import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularGroup
import OrbitComplexity.FlagVarieties.Foundations.TypeA.MatrixBruhatDecomposition
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Block
import OrbitComplexity.ReductiveGroups.GLn.PairEmbedding

/-! # Solvable subgroups containing the upper-triangular group -/

namespace ReductiveGroups.GLn
open FlagVarieties.Foundations

open scoped commutatorElement
open Matrix

section Overgroup

variable {F : Type*} [Field F] {n : ℕ}

/-- For these parameters,

```lean
(Matrix.transvection i j t).IsUpperTriangular
```
-/
theorem transvection_isUpperTriangular {i j : Fin n} (hij : i < j) (t : F) :
    (Matrix.transvection i j t).IsUpperTriangular := by
  intro a b hab
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h1 : a ≠ b := fun h => (lt_irrefl a) (h ▸ hab)
  have h2 : ¬(i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hab hij
  simp [h1, h2]

/-- For these parameters,

```lean
Matrix.transvection i j (1 : F) ≠ 1
```
-/
theorem transvection_ne_one {i j : Fin n} (hij : i ≠ j) :
    Matrix.transvection i j (1 : F) ≠ 1 := by
  intro h
  have := congrFun (congrFun h i) j
  simp [Matrix.transvection, hij] at this

/-- The equality is

```lean
(pivotMatrix (K := F) w : Matrix (Fin n) (Fin n) F) = (w⁻¹).toPEquiv.toMatrix
```
-/
theorem pivotMatrix_eq_toMatrix (w : Equiv.Perm (Fin n)) :
    (pivotMatrix (K := F) w : Matrix (Fin n) (Fin n) F) = (w⁻¹).toPEquiv.toMatrix := by
  ext a b
  rcases eq_or_ne (w b) a with h | h
  · simp [pivotMatrix, h, Equiv.symm_apply_eq]
  · simp [pivotMatrix, h, Ne.symm h, Equiv.symm_apply_eq]

/-- The equality is

```lean
(pivotMatrix (K := F) (1 : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) F) = 1
```
-/
theorem pivotMatrix_one : (pivotMatrix (K := F) (1 : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) F) = 1 := by
  rw [pivotMatrix_eq_toMatrix, inv_one]
  exact PEquiv.toMatrix_refl

/-- Conjugating by a permutation matrix permutes the indices of a matrix. -/
theorem perm_conj (w : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) F) :
    (w⁻¹).toPEquiv.toMatrix * M * w.toPEquiv.toMatrix =
      M.submatrix (w⁻¹ : Equiv.Perm (Fin n)) (w⁻¹ : Equiv.Perm (Fin n)) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

/-- The equality is

```lean
(Matrix.transvection a b t).submatrix (w⁻¹ : Equiv.Perm (Fin n))
        (w⁻¹ : Equiv.Perm (Fin n)) = Matrix.transvection (w a) (w b) t
```
-/
theorem transvection_submatrix_perm (w : Equiv.Perm (Fin n)) (a b : Fin n) (t : F) :
    (Matrix.transvection a b t).submatrix (w⁻¹ : Equiv.Perm (Fin n))
        (w⁻¹ : Equiv.Perm (Fin n)) = Matrix.transvection (w a) (w b) t := by
  ext x y
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]

/-- A nontrivial permutation has an inversion. -/
theorem exists_inversion (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ a b : Fin n, a < b ∧ w b < w a := by
  by_contra h
  push Not at h
  have hmono : StrictMono w := by
    intro a b hab
    exact lt_of_le_of_ne (h a b hab) (fun he => (ne_of_lt hab) (w.injective he))
  have hmono' : StrictMono (w⁻¹ : Equiv.Perm (Fin n)) := by
    intro a b hab
    by_contra hle
    push Not at hle
    have := hmono.monotone hle
    simp only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact absurd hab (not_lt.mpr this)
  apply hw
  ext a
  have h1 : a ≤ w a := hmono.le_apply
  have h2 : a ≤ (w⁻¹ : Equiv.Perm (Fin n)) a := hmono'.le_apply
  have h3 : w a ≤ a := by
    have := hmono.monotone h2
    simpa using this
  simp [le_antisymm h3 h1]

/-- **A solvable subgroup of `GL_n(F)` containing the invertible upper-triangular matrices
consists of upper-triangular matrices.** Here `F` is any field containing an element `c ≠ 0`
with `c² ≠ 1`, for instance any infinite field. -/
theorem le_upperTriangularGroup_of_isSolvable (S : Subgroup (GL (Fin n) F))
    (hS : upperTriangularGroup F n ≤ S) [Group.IsSolvable S] {c : F} (hc0 : c ≠ 0)
    (hc : c ^ 2 ≠ 1) : S ≤ upperTriangularGroup F n := by
  intro g hg
  by_contra hgU
  obtain ⟨B, C, w, hB, hC, huB, huC, hdec⟩ :=
    FlagVarieties.Foundations.TypeA.exists_upper_perm_upper_of_isUnit (g : Matrix (Fin n) (Fin n) F)
      g.isUnit
  let Bu : GL (Fin n) F := huB.unit
  let Cu : GL (Fin n) F := huC.unit
  have hBu : Bu ∈ S := hS hB
  have hCu : Cu ∈ S := hS hC
  let P : GL (Fin n) F := Bu⁻¹ * g * Cu⁻¹
  have hP : P ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hBu) hg) (S.inv_mem hCu)
  have hPcoe : (P : Matrix (Fin n) (Fin n) F) = pivotMatrix (K := F) w := by
    have hB' : (Bu : Matrix (Fin n) (Fin n) F) = B := huB.unit_spec
    have hC' : (Cu : Matrix (Fin n) (Fin n) F) = C := huC.unit_spec
    simp only [P, Units.val_mul]
    rw [hdec, ← hB', ← hC']
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  by_cases hw : w = 1
  · apply hgU
    change (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular
    rw [hdec, hw, pivotMatrix_one, Matrix.mul_one]
    exact Matrix.BlockTriangular.mul hB hC
  obtain ⟨a, b, hab, hwab⟩ := exists_inversion w hw
  have hne : w b ≠ w a := ne_of_lt hwab
  -- the lower root element `1 + t e_{w a, w b}` lies in `S`
  have hPinv : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      w.toPEquiv.toMatrix := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hPcoe, pivotMatrix_eq_toMatrix]
    have h := perm_conj (F := F) w 1
    rw [Matrix.mul_one, Matrix.submatrix_one_equiv (w⁻¹ : Equiv.Perm (Fin n))] at h
    exact h
  have hY : ∀ t : F, pairEmbedding (w b) (w a) hne (elemY t) ∈ S := by
    intro t
    have hconj : pairEmbedding (w b) (w a) hne (elemY t) =
        P * pairEmbedding a b (ne_of_lt hab) (elemX t) * P⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_pairEmbedding_elemY, coe_pairEmbedding_elemX,
        hPcoe, hPinv, pivotMatrix_eq_toMatrix, perm_conj, transvection_submatrix_perm]
    rw [hconj]
    refine S.mul_mem (S.mul_mem hP (hS ?_)) (S.inv_mem hP)
    change ((pairEmbedding a b (ne_of_lt hab) (elemX t) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).IsUpperTriangular
    rw [coe_pairEmbedding_elemX]
    exact transvection_isUpperTriangular hab t
  have hX : ∀ t : F, pairEmbedding (w b) (w a) hne (elemX t) ∈ S := by
    intro t
    apply hS
    change ((pairEmbedding (w b) (w a) hne (elemX t) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).IsUpperTriangular
    rw [coe_pairEmbedding_elemX]
    exact transvection_isUpperTriangular hwab t
  have hone := map_elemX_one_eq_one (pairEmbedding (w b) (w a) hne) S hX hY hc0 hc
  have hmat := congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) hone
  simp only [coe_pairEmbedding_elemX, Units.val_one] at hmat
  exact transvection_ne_one hne hmat

/-- An infinite field contains an element `c ≠ 0` with `c² ≠ 1`. -/
theorem exists_sq_ne_one [Infinite F] : ∃ c : F, c ≠ 0 ∧ c ^ 2 ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨c, hc.1, fun h => ?_⟩
  have h' : (c - 1) * (c + 1) = c ^ 2 - 1 := by ring
  rw [h, sub_self] at h'
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact hc.2.1 (sub_eq_zero.mp h1)
  · exact hc.2.2 (eq_neg_of_add_eq_zero_left h1)

end Overgroup

end GLn
