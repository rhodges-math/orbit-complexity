import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Reflection

/-!
# The geometric bilinear form of a Coxeter matrix

The free real vector space on the simple indices carries the symmetric form with Gram entries
`-cos (π / mᵢⱼ)`. Its simple roots have squared length one and define linear reflections.

## Main definitions

* `geometricRoot`: the basis vector at a simple index.
* `geometricForm`: the bilinear form determined by the Coxeter matrix.
* `geometricCoroot`: the linear functional twice pairing with a simple root.
* `geometricReflection`: the reflection in a simple root.

## Main results

* `geometricForm_isSymm`: the geometric form is symmetric.
* `geometricReflection_form`: simple reflections preserve the geometric form.
* `geometricReflection_commute`: exponent two gives commuting simple reflections.

## Implementation notes

The space is a finitely supported function space, so the simple index type may be infinite. An
infinite Coxeter exponent is represented by `0`, for which real division gives Gram entry `-1`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), Chapter 4.
-/

namespace BruhatIntervals

variable {S : Type*} (M : CoxeterMatrix S)

/-- The simple root at `i` in the free real vector space on the simple indices. -/
noncomputable def geometricRoot (i : S) : S →₀ ℝ := Finsupp.single i 1

/-- The geometric bilinear form with Gram entries `-cos (π / mᵢⱼ)`. -/
noncomputable def geometricForm : LinearMap.BilinForm ℝ (S →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun i =>
    Finsupp.linearCombination ℝ (fun j => -Real.cos (Real.pi / (M i j : ℝ))))

/-- The value of the geometric form on two simple roots is its Coxeter Gram entry. -/
theorem geometricForm_root (i j : S) :
    geometricForm M (geometricRoot i) (geometricRoot j) =
      -Real.cos (Real.pi / (M i j : ℝ)) := by
  simp only [geometricForm, geometricRoot, Finsupp.linearCombination_single, one_smul]

/-- Every simple root has squared length one for the geometric form. -/
theorem geometricForm_root_self (i : S) :
    geometricForm M (geometricRoot i) (geometricRoot i) = 1 := by
  rw [geometricForm_root, M.diagonal]
  simp only [Nat.cast_one, div_one, Real.cos_pi, neg_neg]

/-- The geometric bilinear form is symmetric. -/
theorem geometricForm_isSymm : (geometricForm M).IsSymm := by
  apply (LinearMap.BilinForm.isSymm_iff_basis (Finsupp.basisSingleOne)).mpr
  intro i j
  change geometricForm M (geometricRoot i) (geometricRoot j) =
    geometricForm M (geometricRoot j) (geometricRoot i)
  rw [geometricForm_root, geometricForm_root, M.symmetric]

/-- The coroot functional of a simple root is twice its pairing with the geometric form. -/
noncomputable def geometricCoroot (i : S) : Module.Dual ℝ (S →₀ ℝ) :=
  (2 : ℝ) • geometricForm M (geometricRoot i)

/-- Evaluating a simple coroot on a simple root gives twice the corresponding Gram entry. -/
theorem geometricCoroot_root (i j : S) :
    geometricCoroot M i (geometricRoot j) =
      -2 * Real.cos (Real.pi / (M i j : ℝ)) := by
  simp only [geometricCoroot, LinearMap.smul_apply, smul_eq_mul, geometricForm_root]
  ring

/-- A simple coroot takes the value two on its simple root. -/
theorem geometricCoroot_root_self (i : S) :
    geometricCoroot M i (geometricRoot i) = 2 := by
  simp only [geometricCoroot, LinearMap.smul_apply, smul_eq_mul, geometricForm_root_self,
    mul_one]

/-- The linear reflection in a simple root of the geometric space. -/
noncomputable def geometricReflection (i : S) : (S →₀ ℝ) ≃ₗ[ℝ] (S →₀ ℝ) :=
  Module.reflection (geometricCoroot_root_self M i)

/-- A simple reflection subtracts twice the pairing with its simple root. -/
theorem geometricReflection_apply (i : S) (x : S →₀ ℝ) :
    geometricReflection M i x =
      x - (2 * geometricForm M (geometricRoot i) x) • geometricRoot i := by
  simp only [geometricReflection, Module.reflection_apply, geometricCoroot,
    LinearMap.smul_apply, smul_eq_mul]

/-- A simple reflection sends its simple root to its negative. -/
theorem geometricReflection_root_self (i : S) :
    geometricReflection M i (geometricRoot i) = -geometricRoot i :=
  Module.reflection_apply_self (geometricCoroot_root_self M i)

/-- A simple reflection has square equal to the identity. -/
theorem geometricReflection_sq (i : S) : geometricReflection M i ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  rw [pow_two, LinearEquiv.mul_apply]
  exact Module.involutive_reflection (geometricCoroot_root_self M i) x

/-- Simple roots are linearly independent in the geometric space. -/
theorem geometricRoot_linearIndependent : LinearIndependent ℝ (geometricRoot (S := S)) :=
  Finsupp.basisSingleOne.linearIndependent

/-- Each simple reflection preserves the geometric bilinear form. -/
theorem geometricReflection_form (i : S) (x y : S →₀ ℝ) :
    geometricForm M (geometricReflection M i x) (geometricReflection M i y) =
      geometricForm M x y := by
  simp only [geometricReflection_apply, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, geometricForm_root_self]
  rw [(geometricForm_isSymm M).eq x (geometricRoot i)]
  ring

/-- An exponent two in the Coxeter matrix gives commuting simple geometric reflections. -/
theorem geometricReflection_commute {i j : S} (h : M i j = 2) :
    Commute (geometricReflection M i) (geometricReflection M j) := by
  have hij : geometricCoroot M i (geometricRoot j) = 0 := by
    rw [geometricCoroot_root, h]
    simp only [Nat.cast_ofNat, Real.cos_pi_div_two, mul_zero]
  have hji : geometricCoroot M j (geometricRoot i) = 0 := by
    rw [geometricCoroot_root, M.symmetric j i, h]
    simp only [Nat.cast_ofNat, Real.cos_pi_div_two, mul_zero]
  change geometricReflection M i * geometricReflection M j =
    geometricReflection M j * geometricReflection M i
  apply LinearEquiv.ext
  intro x
  simp only [geometricReflection, LinearEquiv.mul_apply, Module.reflection_apply,
    map_sub, map_smul, hij, hji, zero_smul, sub_zero]
  abel

end BruhatIntervals
