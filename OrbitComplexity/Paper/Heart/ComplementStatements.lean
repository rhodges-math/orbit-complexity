import OrbitComplexity.Paper.Heart.Complement
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The complementary parabolic unipotent subgroup preserves the heart.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u

/-- The complementary parabolic unipotent subgroup preserves the heart. -/
theorem complement_stable_heart {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup) :
    ∀ (u : G.points),
      u ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G u • q ∈
          Set.range (Variety.mapPoints (heartInclusion G I w)) :=
  complement_heart_stable G I w

/-- The complementary parabolic unipotent subgroup preserves the heart.
The base field is the complex numbers. -/
theorem complement_stable_heart_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    ∀ (u : G.points),
      u ∈ G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) →
      ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) →
        reductivePointsMulEquiv G u • q ∈
          Set.range (Variety.mapPoints (heartInclusion G I w)) :=
  complement_stable_heart G I w

end SchubertOrbits
