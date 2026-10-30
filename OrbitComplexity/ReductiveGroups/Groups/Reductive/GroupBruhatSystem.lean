import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots
import OrbitComplexity.ReductiveGroups.Groups.Cells.SchubertCellRankOne

/-!
# Root-data Bruhat multiplication relations

The fixed Borel, torus and rank-one root maps give a Bruhat system whose word
representatives coincide with the Weyl representatives of the reductive datum.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The root reflection point selected by the corresponding rank-one subgroup. -/
def reflectionPoint (r : G.rootIndex) : G.points :=
  characterReflectionPoint G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive (G.characterRootEquiv.symm r)

/-- The positive additive root map chosen in the simple-root rank-one pair. -/
def simpleRootMap (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (characterSl2PairChoice G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive (G.characterRootEquiv.symm i.val)).1

/-- The negative additive root map chosen in the simple-root rank-one pair. -/
def negativeSimpleRootMap (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (characterSl2PairChoice G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive (G.characterRootEquiv.symm i.val)).2

/-- An ambient point transports root subspaces by a specified permutation of roots. -/
def rootPointTransport (g : G.points) (σ : Equiv.Perm G.rootIndex) : Prop :=
  ∀ r, (G.rootWeightSpace r).map
      ((affineGroupAdjointLieEquiv g).toLinearEquiv : G.tangent →ₗ[K] G.tangent) =
    G.rootWeightSpace (σ r)

/-- The chosen Borel, torus and simple-root pairs satisfy the Bruhat multiplication relations. -/
theorem isBruhatSystem : IsBruhatSystem G.rootBase G.borelPoints G.torusPoints
    G.reflectionPoint G.rootPointTransport
    (fun i c => gaParameterPoint (G.simpleRootMap i) c)
    (fun i c => gaParameterPoint (G.negativeSimpleRootMap i) c) :=
  reductive_isBruhatSystem G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
    G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- The word representative from the Bruhat system is the chosen Weyl representative. -/
theorem weylPoint_eq (w : G.weylGroup) :
    G.weylPoint w = weylElementPoint G.reflectionPoint G.rootBase w := by
  rfl

end ReductiveGroups.ReductiveGroupData
