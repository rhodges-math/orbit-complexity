import OrbitComplexity.ReductiveGroups.GLn.UpperTriangularGroup
import OrbitComplexity.FlagVarieties.Foundations.TypeA.MatrixBruhatDecomposition
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Block
import OrbitComplexity.ReductiveGroups.GLn.TwoByTwo

/-! # Embedding a two-dimensional general linear group along a pair of coordinates -/

namespace ReductiveGroups.GLn
open FlagVarieties.Foundations

open scoped commutatorElement
open Matrix

section Embedding

variable {F : Type*} [Field F] {n : ℕ}

/-- `Fin 2` enumerates a pair of distinct indices. -/
def pairEquiv (i j : Fin n) (hij : i ≠ j) : Fin 2 ≃ {k : Fin n // k = i ∨ k = j} where
  toFun a := if a = 0 then ⟨i, Or.inl rfl⟩ else ⟨j, Or.inr rfl⟩
  invFun k := if k.1 = i then 0 else 1
  left_inv a := by
    fin_cases a
    · simp
    · simp [Ne.symm hij]
  right_inv k := by
    obtain ⟨k, hk | hk⟩ := k
    · subst hk
      simp
    · subst hk
      simp [Ne.symm hij]

/-- Split the indices into the pair `{i, j}` and its complement. -/
def pairSplit (i j : Fin n) (hij : i ≠ j) :
    Fin n ≃ Fin 2 ⊕ {k : Fin n // ¬(k = i ∨ k = j)} :=
  (Equiv.sumCompl (fun k : Fin n => k = i ∨ k = j)).symm.trans
    (Equiv.sumCongr (pairEquiv i j hij).symm (Equiv.refl _))

/-- The equality is

```lean
pairSplit i j hij i = Sum.inl 0
```
-/
theorem pairSplit_left (i j : Fin n) (hij : i ≠ j) : pairSplit i j hij i = Sum.inl 0 := by
  simp [pairSplit, pairEquiv]

/-- The equality is

```lean
pairSplit i j hij j = Sum.inl 1
```
-/
theorem pairSplit_right (i j : Fin n) (hij : i ≠ j) : pairSplit i j hij j = Sum.inl 1 := by
  simp [pairSplit, pairEquiv, Ne.symm hij]

/-- The equality is

```lean
pairSplit i j hij k = Sum.inr ⟨k, hk⟩
```
-/
theorem pairSplit_other (i j : Fin n) (hij : i ≠ j) {k : Fin n} (hk : ¬(k = i ∨ k = j)) :
    pairSplit i j hij k = Sum.inr ⟨k, hk⟩ := by
  simp [pairSplit, hk]

/-- The block embedding of `2 × 2` matrices into `n × n` matrices along the pair `(i, j)`, with
the identity on the complementary indices. It is multiplicative and unital. -/
def pairMatrixEmbedding (i j : Fin n) (hij : i ≠ j) :
    Matrix (Fin 2) (Fin 2) F →* Matrix (Fin n) (Fin n) F where
  toFun M := (Matrix.fromBlocks M 0 0 (1 : Matrix {k : Fin n // ¬(k = i ∨ k = j)}
    {k : Fin n // ¬(k = i ∨ k = j)} F)).submatrix (pairSplit i j hij) (pairSplit i j hij)
  map_one' := by
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  map_mul' M N := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

/-- The embedding of `GL_2` into `GL_n` along the pair `(i, j)`. -/
def pairEmbedding (i j : Fin n) (hij : i ≠ j) : GL (Fin 2) F →* GL (Fin n) F :=
  Units.map (pairMatrixEmbedding i j hij)

/-- The equality is

```lean
pairMatrixEmbedding i j hij M a b =
      Matrix.fromBlocks M 0 0 (1 : Matrix {k : Fin n // ¬(k = i ∨ k = j)}
        {k : Fin n // ¬(k = i ∨ k = j)} F) (pairSplit i j hij a) (pairSplit i j hij b)
```
-/
theorem pairMatrixEmbedding_apply (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Fin 2) (Fin 2) F) (a b : Fin n) :
    pairMatrixEmbedding i j hij M a b =
      Matrix.fromBlocks M 0 0 (1 : Matrix {k : Fin n // ¬(k = i ∨ k = j)}
        {k : Fin n // ¬(k = i ∨ k = j)} F) (pairSplit i j hij a) (pairSplit i j hij b) :=
  rfl

/-- Entrywise description of a matrix that is the identity off the pair `{i, j}`. -/
theorem pairMatrixEmbedding_eq (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Fin 2) (Fin 2) F) (N : Matrix (Fin n) (Fin n) F)
    (hii : N i i = M 0 0) (hij' : N i j = M 0 1) (hji : N j i = M 1 0) (hjj : N j j = M 1 1)
    (hoff : ∀ a b, ¬(a = i ∨ a = j) ∨ ¬(b = i ∨ b = j) → N a b = if a = b then 1 else 0) :
    pairMatrixEmbedding i j hij M = N := by
  ext a b
  rw [pairMatrixEmbedding_apply]
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rw [pairSplit_left, hii]; rfl
      · rw [pairSplit_left, pairSplit_right, hij']; rfl
      · rw [pairSplit_left, pairSplit_right, hji]; rfl
      · rw [pairSplit_right, hjj]; rfl
    · rw [pairSplit_other i j hij hb, hoff a b (Or.inr hb)]
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      rcases ha with rfl | rfl
      · rw [pairSplit_left, ite_eq_right hab]; rfl
      · rw [pairSplit_right, ite_eq_right hab]; rfl
  · rw [pairSplit_other i j hij ha, hoff a b (Or.inl ha)]
    by_cases hb : b = i ∨ b = j
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [ite_eq_right hab]
      rcases hb with rfl | rfl
      · rw [pairSplit_left]; rfl
      · rw [pairSplit_right]; rfl
    · rw [pairSplit_other i j hij hb]
      change (1 : Matrix {k : Fin n // ¬(k = i ∨ k = j)}
        {k : Fin n // ¬(k = i ∨ k = j)} F) ⟨a, ha⟩ ⟨b, hb⟩ = _
      rw [Matrix.one_apply]
      simp only [Subtype.mk.injEq]

/-- The equality is

```lean
((pairEmbedding i j hij (elemX t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.transvection i j t
```
-/
theorem coe_pairEmbedding_elemX (i j : Fin n) (hij : i ≠ j) (t : F) :
    ((pairEmbedding i j hij (elemX t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.transvection i j t := by
  change pairMatrixEmbedding i j hij !![1, t; 0, 1] = _
  apply pairMatrixEmbedding_eq
  · simp [Matrix.transvection, Ne.symm hij]
  · simp [Matrix.transvection, Matrix.one_apply_ne hij]
  · simp [Matrix.transvection, Matrix.one_apply_ne (Ne.symm hij), hij]
  · simp [Matrix.transvection, hij]
  · intro a b hab
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    rcases hab with ha | hb
    · have : ¬(i = a ∧ j = b) := fun h => ha (Or.inl h.1.symm)
      simp [this]
    · have : ¬(i = a ∧ j = b) := fun h => hb (Or.inr h.2.symm)
      simp [this]

/-- The equality is

```lean
((pairEmbedding i j hij (elemY t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.transvection j i t
```
-/
theorem coe_pairEmbedding_elemY (i j : Fin n) (hij : i ≠ j) (t : F) :
    ((pairEmbedding i j hij (elemY t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.transvection j i t := by
  change pairMatrixEmbedding i j hij !![1, 0; t, 1] = _
  apply pairMatrixEmbedding_eq
  · simp [Matrix.transvection, Ne.symm hij]
  · simp [Matrix.transvection, Matrix.one_apply_ne hij, hij]
  · simp [Matrix.transvection, Matrix.one_apply_ne (Ne.symm hij)]
  · simp [Matrix.transvection, hij]
  · intro a b hab
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    rcases hab with ha | hb
    · have : ¬(j = a ∧ i = b) := fun h => ha (Or.inr h.1.symm)
      simp [this]
    · have : ¬(j = a ∧ i = b) := fun h => hb (Or.inl h.2.symm)
      simp [this]

end Embedding

end GLn
