import Batteries.Tactic.Lint
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Span.Basic

/-! # Group identities for two root-curve charts

The identities here apply to arbitrary groups, actions, and linear maps. They keep the
coset and inverse-transport calculations independent of the group scheme being used.
-/

namespace SchubertGeometry

universe u v w

/-- Conjugate subgroup membership is the stabilizer equation for a left coset. -/
theorem rootCurve_coset_fixed {Γ : Type u} [Group Γ] (H : Subgroup Γ)
    (n g : Γ) (hg : n⁻¹ * g * n ∈ H) :
    g • (QuotientGroup.mk n : Γ ⧸ H) = QuotientGroup.mk n := by
  change (QuotientGroup.mk (g * n) : Γ ⧸ H) = QuotientGroup.mk n
  apply QuotientGroup.eq.mpr
  have he : (g * n)⁻¹ * n = (n⁻¹ * g * n)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [he]
  exact H.inv_mem hg

/-- The two stabilizer factors in a four-factor decomposition disappear on an orbit. -/
theorem rootCurve_action_factor {Γ : Type u} {X : Type v} [Group Γ]
    [MulAction Γ X] (l u n d : Γ) (x : X)
    (hfactor : l = u * n * d * u) (hu : u • x = x) (hd : d • x = x) :
    l • x = u • (n • x) := by
  rw [hfactor, mul_smul, mul_smul, mul_smul, hu, hd]

/-- A left inverse transports a submodule equality back without unfolding its concrete maps. -/
theorem rootCurve_map_inverse {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] (A B : Submodule R M) (f g : M →ₗ[R] M)
    (hAB : A.map f = B) (hgf : g.comp f = LinearMap.id) : B.map g = A := by
  rw [← hAB, ← Submodule.map_comp, hgf, Submodule.map_id]

end SchubertGeometry
