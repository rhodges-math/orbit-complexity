import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap
import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixLinearFormExtension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Borel Torus Unipotent Matrix

Elementary facts on upper triangular matrices used for the torus and
unipotent factorization of Borel points: diagonals of powers, unipotent and
nilpotent upper triangular matrices, finite logarithms of unipotent upper
triangular matrices, and the algebra automorphism given by a change of basis. -/

noncomputable section
namespace ReductiveGroups.TorusUnipotent

open Module

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- For these parameters,

```lean
matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) R)
```
-/
theorem matrixUpperGap_zero_one :
    matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  apply Matrix.one_apply_ne
  intro h
  subst h
  omega

/-- For these parameters,

```lean
matrixUpperGap d (A + C)
```
-/
theorem matrixUpperGap_add {d : ℕ} {A C : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap d A) (hC : matrixUpperGap d C) :
    matrixUpperGap d (A + C) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hC i j hij, add_zero]

/-- For these parameters,

```lean
matrixUpperGap d (c • A)
```
-/
theorem matrixUpperGap_smul {d : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap d A) (c : R) :
    matrixUpperGap d (c • A) := by
  intro i j hij
  simp only [Matrix.smul_apply, hA i j hij, smul_eq_mul, mul_zero]

/-- For these parameters,

```lean
matrixUpperGap d (0 : Matrix (Fin n) (Fin n) R)
```
-/
theorem matrixUpperGap_zero_matrix {d : ℕ} :
    matrixUpperGap d (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j _
  rfl

/-- For these parameters,

```lean
matrixUpperGap d (∑ k ∈ s, A k)
```
-/
theorem matrixUpperGap_sum {d : ℕ} {κ : Type*} (s : Finset κ)
    (A : κ → Matrix (Fin n) (Fin n) R) (hA : ∀ k ∈ s, matrixUpperGap d (A k)) :
    matrixUpperGap d (∑ k ∈ s, A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (matrixUpperGap_zero_matrix (R := R) (n := n) (d := d))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact matrixUpperGap_add (hA a (Finset.mem_insert_self a s))
        (ih fun k hk => hA k (Finset.mem_insert_of_mem hk))

/-- Powers of a matrix with gap `d` have gap `d * k` (and gap `0` for `k = 0`). -/
theorem matrixUpperGap_pow {d : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap d A) (k : ℕ) :
    matrixUpperGap (d * k) (A ^ k) := by
  induction k with
  | zero => simpa using (matrixUpperGap_zero_one (R := R) (n := n))
  | succ k ih =>
      rw [pow_succ, Nat.mul_succ]
      exact matrixUpperGap_mul ih hA

/-- The diagonal of a power of an upper triangular matrix is the power of
its diagonal. -/
theorem upperMatrix_pow_diag {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = A i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, upperMatrix_mul_diag (by simpa using matrixUpperGap_pow hA k) hA i,
        ih, pow_succ]

/-- For these parameters,

```lean
matrixUpperGap 0 (A - 1)
```
-/
theorem matrixUpperGap_sub_one {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) : matrixUpperGap 0 (A - 1) :=
  matrixUpperGap_sub hA matrixUpperGap_zero_one

/-- An upper triangular matrix with zero diagonal is strictly upper triangular. -/
theorem matrixUpperGap_one_of_diag_eq_zero {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hd : ∀ i, A i i = 0) : matrixUpperGap 1 A := by
  intro i j hij
  by_cases h : j = i
  · subst h
    exact hd j
  · exact hA i j (by
      have : j.val ≠ i.val := fun e => h (Fin.ext e)
      omega)

/-- A strictly upper triangular `n × n` matrix has vanishing `n`-th power. -/
theorem pow_card_eq_zero_of_matrixUpperGap_one {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 1 A) : A ^ n = 0 := by
  apply matrixUpperGap_eq_zero (matrixUpperGap_pow hA n)
  omega

/-- The diagonal of an upper triangular matrix with a vanishing power is
nilpotent, hence zero in a reduced ring. -/
theorem upperMatrix_diag_eq_zero_of_pow_eq_zero [IsReduced R]
    {A : Matrix (Fin n) (Fin n) R} (hA : matrixUpperGap 0 A)
    {m : ℕ} (hm : A ^ m = 0) (i : Fin n) : A i i = 0 := by
  have h : A i i ^ m = 0 := by
    rw [← upperMatrix_pow_diag hA m i, hm]
    rfl
  exact IsReduced.eq_zero _ ⟨m, h⟩

/-- An upper triangular unipotent matrix has unit diagonal. -/
theorem UpperMatrix.diag_eq_one_of_sub_one_pow_eq_zero [IsReduced R]
    {A : Matrix (Fin n) (Fin n) R} (hA : matrixUpperGap 0 A)
    {m : ℕ} (hm : (A - 1) ^ m = 0) (i : Fin n) : A i i = 1 := by
  have h := upperMatrix_diag_eq_zero_of_pow_eq_zero (matrixUpperGap_sub_one hA) hm i
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
  exact sub_eq_zero.mp h

/-- An upper triangular matrix with unit diagonal differs from the identity
by a strictly upper triangular matrix. -/
theorem matrixUpperGap_one_sub_one {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hd : ∀ i, A i i = 1) :
    matrixUpperGap 1 (A - 1) := by
  apply matrixUpperGap_one_of_diag_eq_zero (matrixUpperGap_sub_one hA)
  intro i
  rw [Matrix.sub_apply, Matrix.one_apply_eq, hd i, sub_self]

/-- Finite logarithm polynomials of a unipotent upper triangular matrix are
strictly upper triangular. -/
theorem matrixUpperGap_one_finite_logarithm {A : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hd : ∀ i, A i i = 1) (r : ℕ) (c : ℕ → R) :
    matrixUpperGap 1 (∑ k ∈ Finset.range r, c k • (A - 1) ^ (k + 1)) := by
  apply matrixUpperGap_sum
  intro k _
  apply matrixUpperGap_smul
  exact matrixUpperGap_mono (matrixUpperGap_pow (matrixUpperGap_one_sub_one hA hd) (k + 1))
    (by omega)

/-- For upper triangular matrices whose product is the identity, the
diagonal entries are mutually inverse. -/
theorem upperMatrix_diag_mul_eq_one {A C : Matrix (Fin n) (Fin n) R}
    (hA : matrixUpperGap 0 A) (hC : matrixUpperGap 0 C) (h : A * C = 1)
    (i : Fin n) : A i i * C i i = 1 := by
  rw [← upperMatrix_mul_diag hA hC i, h, Matrix.one_apply_eq]

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- Re-expressing a matrix in a basis of `Kⁿ` is a `K`-algebra automorphism
of the matrix algebra. -/
def matrixBasisConj (b : Basis (Fin n) K (Fin n → K)) :
    Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)

/-- The equality is

```lean
matrixBasisConj b A = LinearMap.toMatrix b b (Matrix.toLin' A)
```
-/
theorem matrixBasisConj_apply (b : Basis (Fin n) K (Fin n → K))
    (A : Matrix (Fin n) (Fin n) K) :
    matrixBasisConj b A = LinearMap.toMatrix b b (Matrix.toLin' A) := rfl

/-- One entry of the basis change, as a scalar linear form. -/
def matrixBasisConjEntry (b : Basis (Fin n) K (Fin n → K)) (i j : Fin n) :
    Matrix (Fin n) (Fin n) K →ₗ[K] K :=
  (Matrix.entryLinearMap K K i j).comp (matrixBasisConj b).toLinearMap

/-- The equality is

```lean
matrixBasisConjEntry b i j A = matrixBasisConj b A i j
```
-/
@[simp] theorem matrixBasisConjEntry_apply (b : Basis (Fin n) K (Fin n → K))
    (i j : Fin n) (A : Matrix (Fin n) (Fin n) K) :
    matrixBasisConjEntry b i j A = matrixBasisConj b A i j := rfl

/-- Nilpotence is invariant under the basis change. -/
theorem matrixBasisConj_pow_eq_zero_iff (b : Basis (Fin n) K (Fin n → K))
    (A : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    (matrixBasisConj b A) ^ m = 0 ↔ A ^ m = 0 := by
  rw [← map_pow, map_eq_zero_iff _ (matrixBasisConj b).injective]

end Field

end TorusUnipotent
