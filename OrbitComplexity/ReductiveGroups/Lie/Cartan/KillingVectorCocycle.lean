import OrbitComplexity.ReductiveGroups.Lie.Cartan.KillingCocycle
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Killing Vector Cocycle

Finite-dimensional central cocycles reduce coordinatewise to scalar
cocycles. The resulting functional is a single vector-valued linear map. -/

noncomputable section
namespace ReductiveGroups

variable {K S N : Type*} [Field K] [LieRing S] [LieAlgebra K S]
  [FiniteDimensional K S] [LieAlgebra.IsKilling K S]
  [AddCommGroup N] [Module K N] [FiniteDimensional K N]

/-- Every finite-dimensional vector-valued central cocycle on a Killing
Lie algebra is the value of a linear map on the bracket. -/
theorem killing_vector_cocycle_is_coboundary
    (ω : S →ₗ[K] S →ₗ[K] N)
    (hAlt : ∀ x : S, ω x x = 0)
    (hCocycle : ∀ x y z : S,
      ω ⁅x, y⁆ z + ω ⁅y, z⁆ x + ω ⁅z, x⁆ y = 0) :
    ∃ f : S →ₗ[K] N, ∀ x y : S, ω x y = f ⁅x, y⁆ := by
  classical
  let b := Module.finBasis K N
  have hi (i : Fin (Module.finrank K N)) :
      ∃ f : S →ₗ[K] K, ∀ x y : S, (b.coord i) (ω x y) = f ⁅x, y⁆ := by
    apply killing_cocycle_is_coboundary (ω.compr₂ (b.coord i))
    · intro x
      change (b.coord i) (ω x x) = 0
      rw [hAlt, map_zero]
    · intro x y z
      change (b.coord i) (ω ⁅x, y⁆ z) + (b.coord i) (ω ⁅y, z⁆ x) +
        (b.coord i) (ω ⁅z, x⁆ y) = 0
      rw [← map_add, ← map_add, hCocycle, map_zero]
  choose f hf using hi
  let F : S →ₗ[K] N := {
    toFun := fun x => ∑ i, f i x • b i
    map_add' := by
      intro x y
      simp only [map_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul,
        Finset.smul_sum]
  }
  refine ⟨F, ?_⟩
  intro x y
  change ω x y = ∑ i, f i ⁅x, y⁆ • b i
  calc
    ω x y = ∑ i, (b.coord i) (ω x y) • b i := (b.sum_repr (ω x y)).symm
    _ = _ := by simp only [hf]

end ReductiveGroups
