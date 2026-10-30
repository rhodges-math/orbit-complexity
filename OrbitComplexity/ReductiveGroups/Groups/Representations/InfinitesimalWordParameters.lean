import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWords
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Infinitesimal Word Parameters

Independent square-zero parameters for all leaves of a balanced word.
The full mixed coefficient is a linear map sending the full parameter to 1. -/

noncomputable section
namespace ReductiveGroups
open scoped TensorProduct

universe u
variable (K : Type u) [CommRing K]

/-- One dual number for each leaf, arranged as a balanced tensor product. -/
def InfinitesimalWordAlg : ℕ → CommAlgCat K
  | 0 => CommAlgCat.of K (DualNumber K)
  | n + 1 =>
      let A := InfinitesimalWordAlg n
      CommAlgCat.of K (A ⊗[K] A)

/-- The parameter algebra of a balanced word of depth `n`: the `2^n`-fold tensor power of the dual
numbers `K[ε]`, one square-zero parameter per leaf, as a type. -/
abbrev InfinitesimalWordParameters (n : ℕ) : Type u := InfinitesimalWordAlg K n

/-- Product of the distinct infinitesimal parameters at all leaves. -/
def infinitesimalWordParameter : (n : ℕ) → InfinitesimalWordParameters K n
  | 0 => TrivSqZeroExt.inr (1 : K)
  | n + 1 => infinitesimalWordParameter n ⊗ₜ[K] infinitesimalWordParameter n

/-- Extract the coefficient of the full square-free parameter product. -/
def infinitesimalWordCoefficient :
    (n : ℕ) → InfinitesimalWordParameters K n →ₗ[K] K
  | 0 => TrivSqZeroExt.sndHom K K
  | n + 1 => (TensorProduct.lid K K).toLinearMap.comp
      (TensorProduct.map (infinitesimalWordCoefficient n) (infinitesimalWordCoefficient n))

/-- The equality is

```lean
infinitesimalWordCoefficient K n (infinitesimalWordParameter K n) = 1
```
-/
@[simp] theorem infinitesimalWordCoefficient_parameter (n : ℕ) :
    infinitesimalWordCoefficient K n (infinitesimalWordParameter K n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (TensorProduct.lid K K)
        (TensorProduct.map (infinitesimalWordCoefficient K n) (infinitesimalWordCoefficient K n)
          (infinitesimalWordParameter K n ⊗ₜ[K] infinitesimalWordParameter K n)) = 1
      simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, ih, smul_eq_mul, one_mul]

/-- The equality is

```lean
infinitesimalWordParameter K n * infinitesimalWordParameter K n = 0
```
-/
theorem infinitesimalWordParameter_sq_zero (n : ℕ) :
    infinitesimalWordParameter K n * infinitesimalWordParameter K n = 0 := by
  induction n with
  | zero =>
      change (TrivSqZeroExt.inr (1 : K) : DualNumber K) * TrivSqZeroExt.inr (1 : K) = 0
      exact TrivSqZeroExt.inr_mul_inr (R := K) (1 : K) (1 : K)
  | succ n ih =>
      change (infinitesimalWordParameter K n ⊗ₜ[K] infinitesimalWordParameter K n :
        InfinitesimalWordParameters K n ⊗[K] InfinitesimalWordParameters K n) *
        (infinitesimalWordParameter K n ⊗ₜ[K] infinitesimalWordParameter K n) = 0
      rw [Algebra.TensorProduct.tmul_mul_tmul, ih, TensorProduct.zero_tmul]

/-- For these parameters,

```lean
infinitesimalWordParameter K n ≠ 0
```
-/
theorem infinitesimalWordParameter_ne_zero [Nontrivial K] (n : ℕ) :
    infinitesimalWordParameter K n ≠ 0 := by
  intro hz
  have h := congrArg (infinitesimalWordCoefficient K n) hz
  rw [infinitesimalWordCoefficient_parameter, map_zero] at h
  exact one_ne_zero h

/-- Each leaf has its own square-zero parameter; the two branches use the
two different tensor factors. -/
def infinitesimalWordLeaf :
    (n : ℕ) → DerivedWordIndex n → InfinitesimalWordParameters K n
  | 0, _ => TrivSqZeroExt.inr (1 : K)
  | n + 1, (false, i) =>
      (infinitesimalWordLeaf n i) ⊗ₜ[K] (1 : InfinitesimalWordParameters K n)
  | n + 1, (true, i) =>
      (1 : InfinitesimalWordParameters K n) ⊗ₜ[K] (infinitesimalWordLeaf n i)

/-- The equality is

```lean
infinitesimalWordLeaf K n i * infinitesimalWordLeaf K n i = 0
```
-/
theorem infinitesimalWordLeaf_sq_zero (n : ℕ) (i : DerivedWordIndex n) :
    infinitesimalWordLeaf K n i * infinitesimalWordLeaf K n i = 0 := by
  induction n with
  | zero =>
      change (TrivSqZeroExt.inr (1 : K) : DualNumber K) * TrivSqZeroExt.inr (1 : K) = 0
      exact TrivSqZeroExt.inr_mul_inr (R := K) (1 : K) (1 : K)
  | succ n ih =>
      rcases i with ⟨b, i⟩
      cases b
      · have h : (infinitesimalWordLeaf K n i ⊗ₜ[K] 1 :
          InfinitesimalWordParameters K n ⊗[K] InfinitesimalWordParameters K n) *
          (infinitesimalWordLeaf K n i ⊗ₜ[K] 1) = 0 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, ih, TensorProduct.zero_tmul]
        exact h
      · have h : (1 ⊗ₜ[K] infinitesimalWordLeaf K n i :
          InfinitesimalWordParameters K n ⊗[K] InfinitesimalWordParameters K n) *
          (1 ⊗ₜ[K] infinitesimalWordLeaf K n i) = 0 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, ih, TensorProduct.tmul_zero]
        exact h

/-- The equality is

```lean
infinitesimalWordCoefficient K n (c • infinitesimalWordParameter K n) = c
```
-/
theorem InfinitesimalWordCoefficient.smul_parameter (n : ℕ) (c : K) :
    infinitesimalWordCoefficient K n (c • infinitesimalWordParameter K n) = c := by
  rw [map_smul, infinitesimalWordCoefficient_parameter, smul_eq_mul, mul_one]

/-- The equality is

```lean
infinitesimalWordCoefficient K n 1 = 0
```
-/
@[simp] theorem infinitesimalWordCoefficient_one (n : ℕ) :
    infinitesimalWordCoefficient K n 1 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (TensorProduct.lid K K)
        (TensorProduct.map (infinitesimalWordCoefficient K n) (infinitesimalWordCoefficient K n)
          ((1 : InfinitesimalWordParameters K n) ⊗ₜ[K] (1 : InfinitesimalWordParameters K n))) = 0
      simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, ih, zero_smul]

/-- The equality is

```lean
(infinitesimalWordParameter K n ⊗ₜ[K] (1 : InfinitesimalWordParameters K n)) *
      ((1 : InfinitesimalWordParameters K n) ⊗ₜ[K] infinitesimalWordParameter K n) =
        infinitesimalWordParameter K (n + 1)
```
-/
theorem infinitesimalWordParameter_split (n : ℕ) :
    (infinitesimalWordParameter K n ⊗ₜ[K] (1 : InfinitesimalWordParameters K n)) *
      ((1 : InfinitesimalWordParameters K n) ⊗ₜ[K] infinitesimalWordParameter K n) =
        infinitesimalWordParameter K (n + 1) := by
  change (infinitesimalWordParameter K n ⊗ₜ[K] (1 : InfinitesimalWordParameters K n)) *
      ((1 : InfinitesimalWordParameters K n) ⊗ₜ[K] infinitesimalWordParameter K n) =
        infinitesimalWordParameter K n ⊗ₜ[K] infinitesimalWordParameter K n
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end ReductiveGroups
