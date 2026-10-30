import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularGroup
import OrbitComplexity.FlagVarieties.Foundations.TypeA.MatrixBruhatDecomposition
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Block

/-! # Two-by-two root elements and commutator identities -/

namespace ReductiveGroups.GLn
open FlagVarieties.Foundations

open scoped commutatorElement
open Matrix

section TwoByTwo

variable {F : Type*} [Field F]

/-- The upper root element `x(t)` of `GL_2`. -/
def elemX (t : F) : GL (Fin 2) F :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

/-- The lower root element `y(t)` of `GL_2`. -/
def elemY (t : F) : GL (Fin 2) F :=
  ⟨!![1, 0; t, 1], !![1, 0; -t, 1], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

/-- The diagonal element `diag(c, c⁻¹)` of `GL_2`. -/
def elemD (c : F) (hc : c ≠ 0) : GL (Fin 2) F :=
  ⟨!![c, 0; 0, c⁻¹], !![c⁻¹, 0; 0, c], by simp [Matrix.one_fin_two, hc],
    by simp [Matrix.one_fin_two, hc]⟩

/-- The word `x(c) y(-c⁻¹) x(c) x(-1) y(1) x(-1)` in the root elements. -/
def elemH (c : F) : GL (Fin 2) F :=
  elemX c * elemY (-c⁻¹) * elemX c * (elemX (-1) * elemY 1 * elemX (-1))

/-- The equality is

```lean
elemH c = elemD c hc
```
-/
theorem elemH_eq (c : F) (hc : c ≠ 0) : elemH c = elemD c hc := by
  apply Units.ext
  simp only [elemH, elemX, elemY, elemD, Units.val_mul, Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b
  all_goals simp
  all_goals field_simp
  all_goals norm_num

/-- The equality is

```lean
⁅elemD c hc, elemX s⁆ = elemX ((c ^ 2 - 1) * s)
```
-/
theorem commutator_elemD_elemX (c : F) (hc : c ≠ 0) (s : F) :
    ⁅elemD c hc, elemX s⁆ = elemX ((c ^ 2 - 1) * s) := by
  apply Units.ext
  simp only [commutatorElement_def, elemX, elemD, Units.val_mul, Units.inv_mk,
    Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b
  all_goals simp
  all_goals field_simp
  all_goals ring

/-- The equality is

```lean
⁅(elemD c hc)⁻¹, elemY s⁆ = elemY ((c ^ 2 - 1) * s)
```
-/
theorem commutator_inv_elemD_elemY (c : F) (hc : c ≠ 0) (s : F) :
    ⁅(elemD c hc)⁻¹, elemY s⁆ = elemY ((c ^ 2 - 1) * s) := by
  apply Units.ext
  simp only [commutatorElement_def, elemY, elemD, Units.val_mul, Units.inv_mk,
    Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b
  all_goals simp
  all_goals field_simp
  all_goals ring

/-- If a subgroup `S` of a group contains the images of all root elements of `GL_2` under a
homomorphism, then every term of the derived series of `S` contains them. -/
theorem mem_derivedSeries_of_elem {G : Type*} [Group G] (φ : GL (Fin 2) F →* G)
    (S : Subgroup G) (hX : ∀ t, φ (elemX t) ∈ S) (hY : ∀ t, φ (elemY t) ∈ S)
    {c : F} (hc0 : c ≠ 0) (hc : c ^ 2 ≠ 1) (k : ℕ) :
    ∀ t, (⟨φ (elemX t), hX t⟩ : S) ∈ derivedSeries S k ∧
      (⟨φ (elemY t), hY t⟩ : S) ∈ derivedSeries S k := by
  have hc1 : c ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hc
  induction k with
  | zero =>
      intro t
      simp only [derivedSeries_zero, Subgroup.mem_top, and_self]
  | succ k ih =>
      intro t
      let x : F → S := fun t => ⟨φ (elemX t), hX t⟩
      let y : F → S := fun t => ⟨φ (elemY t), hY t⟩
      let h : S := x c * y (-c⁻¹) * x c * (x (-1) * y 1 * x (-1))
      have hmem : h ∈ derivedSeries S k :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ih c).1 (ih _).2) (ih c).1)
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ih _).1 (ih 1).2) (ih _).1)
      have hcoe : (h : G) = φ (elemD c hc0) := by
        rw [← elemH_eq c hc0]
        simp only [h, x, y, elemH, Subgroup.coe_mul, map_mul]
      set s := t / (c ^ 2 - 1) with hs
      have hts : (c ^ 2 - 1) * s = t := by
        rw [hs]
        field_simp
      rw [derivedSeries_succ]
      constructor
      · have heq : x t = ⁅h, x s⁆ := by
          apply Subtype.ext
          rw [commutatorElement_def]
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hcoe]
          rw [← commutatorElement_def, ← map_commutatorElement, commutator_elemD_elemX, hts]
        have hmem' := Subgroup.commutator_mem_commutator hmem (ih s).1
        rw [← heq] at hmem'
        exact hmem'
      · have heq : y t = ⁅h⁻¹, y s⁆ := by
          apply Subtype.ext
          rw [commutatorElement_def]
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hcoe]
          rw [← map_inv, ← commutatorElement_def, ← map_commutatorElement,
            commutator_inv_elemD_elemY, hts]
        have hmem' := Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hmem) (ih s).2
        rw [← heq] at hmem'
        exact hmem'

/-- A solvable subgroup cannot contain the images of all root elements of `GL_2` unless `x(1)`
maps to the identity. -/
theorem map_elemX_one_eq_one {G : Type*} [Group G] (φ : GL (Fin 2) F →* G)
    (S : Subgroup G) [Group.IsSolvable S] (hX : ∀ t, φ (elemX t) ∈ S)
    (hY : ∀ t, φ (elemY t) ∈ S) {c : F} (hc0 : c ≠ 0) (hc : c ^ 2 ≠ 1) :
    φ (elemX 1) = 1 := by
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := S)
  have h := (mem_derivedSeries_of_elem φ S hX hY hc0 hc k 1).1
  rw [hk, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

end TwoByTwo

end GLn
