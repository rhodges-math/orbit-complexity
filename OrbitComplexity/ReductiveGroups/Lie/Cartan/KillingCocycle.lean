import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Killing Cocycle

Scalar two-cocycles on a finite-dimensional Killing Lie algebra are coboundaries. -/

noncomputable section
namespace ReductiveGroups

variable {K S : Type*} [Field K] [LieRing S] [LieAlgebra K S]
  [FiniteDimensional K S] [LieAlgebra.IsKilling K S]

/-- An alternating scalar-valued Lie two-cocycle on a Killing Lie algebra is evaluation of a
linear functional on the Lie bracket. -/
theorem killing_cocycle_is_coboundary
    (ω : S →ₗ[K] S →ₗ[K] K)
    (hAlt : ∀ x : S, ω x x = 0)
    (hCocycle : ∀ x y z : S,
      ω ⁅x, y⁆ z + ω ⁅y, z⁆ x + ω ⁅z, x⁆ y = 0) :
    ∃ f : S →ₗ[K] K, ∀ x y : S, ω x y = f ⁅x, y⁆ := by
  let κ := killingForm K S
  let e := κ.toDual (LieAlgebra.IsKilling.killingForm_nondegenerate K S)
  let Dlin : S →ₗ[K] S := e.symm.toLinearMap.comp ω
  have hD (x y : S) : κ (Dlin x) y = ω x y := by
    exact LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := LieAlgebra.IsKilling.killingForm_nondegenerate K S) (ω x) y
  have hskew (x y : S) : ω x y = -ω y x := by
    have h := hAlt (x + y)
    simp only [map_add, LinearMap.add_apply, hAlt x, hAlt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  let D : LieDerivation K S S := {
    toLinearMap := Dlin
    leibniz' := by
      intro x y
      apply e.injective
      ext z
      change κ (Dlin ⁅x, y⁆) z = κ (⁅x, Dlin y⁆ - ⁅y, Dlin x⁆) z
      have hinv (a b c : S) : κ ⁅a, b⁆ c = -κ b ⁅a, c⁆ :=
        LieModule.traceForm_apply_lie_apply' K S S a b c
      have h₁ : κ ⁅x, Dlin y⁆ z = ω y ⁅z, x⁆ := by
        rw [hinv]
        rw [← lie_skew z x, map_neg, hD]
      have h₂ : κ ⁅y, Dlin x⁆ z = -ω x ⁅y, z⁆ := by
        rw [hinv, hD]
      have hω : ω ⁅x, y⁆ z = ω x ⁅y, z⁆ + ω y ⁅z, x⁆ := by
        rw [hskew x ⁅y, z⁆, hskew y ⁅z, x⁆]
        linear_combination hCocycle x y z
      rw [hD, hω, map_sub, LinearMap.sub_apply, h₁, h₂]
      abel
  }
  obtain ⟨z, hz⟩ := LieDerivation.IsKilling.exists_eq_ad D
  refine ⟨κ z, ?_⟩
  intro x y
  have hzx : ⁅z, x⁆ = Dlin x := by
    have hx := congrArg (fun E : LieDerivation K S S => E x) hz
    simpa [D] using hx
  calc
    ω x y = κ (Dlin x) y := (hD x y).symm
    _ = κ ⁅z, x⁆ y := by rw [hzx]
    _ = κ z ⁅x, y⁆ := LieModule.traceForm_apply_lie_apply K S S z x y

end ReductiveGroups
