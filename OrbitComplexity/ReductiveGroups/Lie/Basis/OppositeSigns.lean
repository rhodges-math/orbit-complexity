import TauCeti.Algebra.Lie.Weights.Sl2System
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Matching signs on opposite normalized root vectors -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule LieAlgebra.IsKilling TauCeti
universe u v
variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- A sign on one normalized root vector determines the coefficient on its opposite. -/
theorem opposite_signs_equal {x : Weight K H L → L} (hx : IsSl2System x)
    (σ : L ≃ₗ⁅K⁆ L) (α β : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero)
    (a b : K) (ha : a * a = 1)
    (he : σ (x α) = a • x β) (hf : σ (x (-α)) = b • x (-β)) : a = b := by
  have hsource : ⁅⁅x α, x (-α)⁆, x α⁆ = (2 : K) • x α := by
    rw [hx.lie_neg α hα, hx.lie_coroot α α, root_apply_coroot hα]
  have htarget : ⁅⁅x β, x (-β)⁆, x β⁆ = (2 : K) • x β := by
    rw [hx.lie_neg β hβ, hx.lie_coroot β β, root_apply_coroot hβ]
  have hm := congrArg σ hsource
  rw [σ.map_lie, σ.map_lie, map_smul, he, hf] at hm
  simp only [smul_lie, lie_smul, htarget, smul_smul] at hm
  have hscalar : a * (b * a * 2) = 2 * b := by
    calc
      _ = (a * a) * (2 * b) := by ring
      _ = _ := by rw [ha, one_mul]
  rw [hscalar] at hm
  have hcoef : 2 * b = 2 * a := (smul_left_injective K (hx.ne_zero β hβ)) hm
  exact (mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) hcoef).symm

end ReductiveGroups
