import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Root Height Linear Form

The height of a root relative to a base is the restriction of
a linear functional taking value one on every simple root. -/

noncomputable section
namespace ReductiveGroups

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [P.IsRootSystem] (b : P.Base)

/-- The linear functional taking value one on each simple root. -/
def rootHeightLinearForm : M →ₗ[K] K :=
  b.toWeightBasis.constr K (fun _ => 1)

omit [CharZero K] in
/-- The equality is

```lean
rootHeightLinearForm P b (P.root j) = 1
```
-/
@[simp] theorem rootHeightLinearForm_simple (j : b.support) :
    rootHeightLinearForm P b (P.root j) = 1 := by
  rw [← b.toWeightBasis_apply j]
  exact b.toWeightBasis.constr_basis K (fun _ => 1) j

/-- The functional evaluates to the integer root height, cast into `K`. -/
theorem rootHeightLinearForm_root (i : ι) :
    rootHeightLinearForm P b (P.root i) = (b.height i : K) := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  rw [hf, map_sum]
  simp only [map_zsmul]
  have hs : ∀ j ∈ b.support, rootHeightLinearForm P b (P.root j) = 1 := by
    intro j hj
    exact rootHeightLinearForm_simple P b ⟨j, hj⟩
  rw [b.height_eq_sum hf, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j hj]
  simp

/-- Any finite integral linear relation among root vectors gives the
same integral relation among their heights. -/
theorem rootHeight_eq_sum_of_root_eq_sum
    {κ : Type*} [Fintype κ]
    (α : κ → ι) (m : κ → ℤ) (β : ι)
    (h : P.root β = ∑ k, m k • P.root (α k)) :
    b.height β = ∑ k, m k * b.height (α k) := by
  have h' := congrArg (rootHeightLinearForm P b) h
  simp only [map_sum, map_zsmul, rootHeightLinearForm_root] at h'
  have hc : ((b.height β : ℤ) : K) =
      ((∑ k, m k * b.height (α k) : ℤ) : K) := by
    simpa only [Int.cast_sum, Int.cast_mul, zsmul_eq_mul] using h'
  exact Int.cast_injective hc

end ReductiveGroups
