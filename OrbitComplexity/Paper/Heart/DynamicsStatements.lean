import OrbitComplexity.Paper.Heart.Dynamics
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Parabolic and complementary unipotent factors satisfy all three heart orbit rules.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u

/-- Parabolic and complementary unipotent factors satisfy all three heart orbit rules. -/
theorem heart_orbit_dynamics {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∀ (u : G.points),
      u ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) →
      u ≠ 1 → ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G u • q ∉
          Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (∀ (t u : G.points), t ∈ G.torusPoints →
      u ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G w)) →
        q ∉ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G (t * u) • q ∉
          Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (∀ (t u₁ u₂ : G.points), t ∈ G.torusPoints →
      u₁ ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      u₂ ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) →
      ∀ h₁ h₂ : (flagVariety G).points,
        h₁ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        h₂ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G (t * u₁ * u₂) • h₁ = h₂ →
        u₂ = 1 ∧ reductivePointsMulEquiv G (t * u₁) • h₁ = h₂) :=
  ⟨parabolic_smul_not_mem_heart G I w,
    fun t u ht hu q _hq hnot => torus_complement_not_mem_heart G I w t u ht hu q hnot,
    heart_factor_eq_one G I w⟩

/-- Parabolic and complementary unipotent factors satisfy all three heart orbit rules.
The base field is the complex numbers. -/
theorem heart_orbit_dynamics_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∀ (u : G.points),
      u ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) →
      u ≠ 1 → ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G u • q ∉
          Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (∀ (t u : G.points), t ∈ G.torusPoints →
      u ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G w)) →
        q ∉ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G (t * u) • q ∉
          Set.range (Variety.mapPoints (heartInclusion G I w))) ∧
    (∀ (t u₁ u₂ : G.points), t ∈ G.torusPoints →
      u₁ ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      u₂ ∈ G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) →
      ∀ h₁ h₂ : (flagVariety G).points,
        h₁ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        h₂ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G (t * u₁ * u₂) • h₁ = h₂ →
        u₂ = 1 ∧ reductivePointsMulEquiv G (t * u₁) • h₁ = h₂) :=
  heart_orbit_dynamics G I w

end SchubertOrbits
