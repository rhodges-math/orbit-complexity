import OrbitComplexity.Paper.Heart.Complement
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTrivial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Triviality of the complementary unipotent subgroup

The complement subgroup is trivial exactly when its root support is empty.
-/

namespace SchubertOrbits
open ReductiveGroups
universe u

/-- The parabolic-complement subgroup is trivial exactly when its root support is empty. -/
theorem complement_trivial_iff {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) = ⊥ ↔
      complementRootIndices G I w = ∅ :=
  G.rootSubsetPoints_eq_bot_iff _ _ (fun _ hr => hr.2.1)

/-- Complementary unipotent subgroup triviality over the complex numbers. -/
theorem complement_trivial_iff_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) = ⊥ ↔
      complementRootIndices G I w = ∅ :=
  complement_trivial_iff G I w

end SchubertOrbits
