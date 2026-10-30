import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentative

/-!
# Weyl representative points of a reductive group

Chosen products of root reflection points represent the Weyl group in the
normalizer of the maximal torus. Their adjoint action transports each root
character subspace to its Weyl image.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti LieAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A representative of a Weyl element formed from the chosen simple root reflections. -/
def weylPoint (w : G.weylGroup) : G.points :=
  weylRepresentative G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive G.rootBase w

/-- Every chosen Weyl representative normalizes the maximal torus points. -/
theorem weylPoint_mem_normalizer (w : G.weylGroup) :
    G.weylPoint w ∈ Subgroup.normalizer (G.torusPoints : Set G.points) :=
  weylRepresentative_mem_normalizer G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive G.rootBase w

/-- A Weyl representative carries a root-character subspace to the corresponding Weyl image. -/
theorem weylPoint_rootWeightSpace (w : G.weylGroup) (r : G.rootIndex) :
    (G.rootWeightSpace r).map
        ((affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv : G.tangent →ₗ[K] _) =
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w r) :=
  weylRepresentative_characterSpace_map G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive G.rootBase w r

/-- A rational point representing the longest Weyl element. -/
def longestPoint : G.points := G.weylPoint G.longestElement

/-- The representative of the longest Weyl element normalizes the maximal torus. -/
theorem longestPoint_mem_normalizer :
    G.longestPoint ∈ Subgroup.normalizer (G.torusPoints : Set G.points) :=
  G.weylPoint_mem_normalizer G.longestElement

end ReductiveGroupData
