import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPoints
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSystemBridge
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.Longest

/-!
# The root data of a reductive group

The tangent Lie algebra modulo its center has nondegenerate Killing form.
The maximal torus determines a Cartan subalgebra of this quotient, and the
chosen Borel subgroup determines a base of its root system.

## Main definitions

* `ReductiveGroups.ReductiveGroupData.rootSystem`: the root system of the group.
* `ReductiveGroups.ReductiveGroupData.rootBase`: the base selected by the Borel subgroup.
* `ReductiveGroups.ReductiveGroupData.longestElement`: the longest Weyl element.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti LieAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The chosen torus has finite character rank. -/
instance torusIndex_finite : Finite G.torusIndex := G.finiteIndex

/-- The tangent Lie algebra at the identity of the reductive group. -/
abbrev tangent :=
  Derivation K G.coordinateAlgebra (Bialgebra.CounitAlgebra K G.coordinateAlgebra K)

/-- The tangent Lie algebra of a finite type affine group is finite-dimensional. -/
instance tangent_finite : FiniteDimensional K G.tangent :=
  finiteTypeAffineGroup_tangent_finite

/-- The tangent Lie algebra of a reductive group has central solvable radical. -/
instance tangent_hasCentralRadical : LieAlgebra.HasCentralRadical K G.tangent :=
  reductive_tangent_hasCentralRadical G.reductive

/-- The image of the maximal torus tangent in the group tangent algebra. -/
abbrev torusTangent : LieSubalgebra K G.tangent :=
  diagonalizableTangentImage G.torusSplit

/-- The tangent of the maximal torus is a Cartan subalgebra. -/
instance torusTangent_isCartan : G.torusTangent.IsCartanSubalgebra :=
  MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan G.torusIdeal
    G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- The quotient of the tangent Lie algebra by its center. -/
abbrev centerQuotient := G.tangent ⧸ LieAlgebra.center K G.tangent

/-- The center quotient has nondegenerate Killing form. -/
instance centerQuotient_isKilling : LieAlgebra.IsKilling K G.centerQuotient :=
  ReductiveTorusRootSystem.tangent_centerQuotient_isKilling G.reductive

/-- The image of the maximal torus tangent in the center quotient. -/
abbrev cartan : LieSubalgebra K G.centerQuotient :=
  centerQuotientCartan G.torusTangent

/-- The torus image is a Cartan subalgebra of the center quotient. -/
instance cartan_isCartan : G.cartan.IsCartanSubalgebra :=
  ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan G.torusIdeal
    G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- The finite index type of the roots of the chosen Cartan subalgebra. -/
abbrev rootIndex : Type u := G.cartan.root

/-- The root system of the reductive group relative to its chosen maximal torus. -/
abbrev rootSystem : RootPairing G.rootIndex K (Module.Dual K G.cartan) G.cartan :=
  LieAlgebra.IsKilling.rootSystem G.cartan

/-- The multiplicative character group of the split maximal torus. -/
abbrev characters : Type u := Multiplicative (G.torusIndex →₀ ℤ)

/-- Nonidentity occurring torus characters correspond to roots of the center quotient. -/
def characterRootEquiv :
    {α : G.characters // affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ ∧ α ≠ 1} ≃
      G.rootIndex :=
  ReductiveCharacterRoots.characterCenterQuotientRootEquiv G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- The torus character corresponding to a root. -/
def rootCharacter (r : G.rootIndex) : G.characters := (G.characterRootEquiv.symm r).val

/-- The torus-character subspace in the original tangent algebra corresponding to a root. -/
def rootWeightSpace (r : G.rootIndex) : Submodule K G.tangent :=
  affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)

/-- A root character is nontrivial. -/
theorem rootCharacter_ne_one (r : G.rootIndex) : G.rootCharacter r ≠ 1 :=
  (G.characterRootEquiv.symm r).property.2

/-- The character space associated with a root is nonzero. -/
theorem rootWeightSpace_ne_bot (r : G.rootIndex) : G.rootWeightSpace r ≠ ⊥ :=
  (G.characterRootEquiv.symm r).property.1

/-- Every root-character subspace in the reductive group tangent algebra is one-dimensional. -/
theorem rootWeightSpace_finrank (r : G.rootIndex) : Module.finrank K (G.rootWeightSpace r) = 1 :=
  ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive (G.rootCharacter r)
    (G.rootCharacter_ne_one r) (G.rootWeightSpace_ne_bot r)

/-- The base of the root system determined by the chosen Borel subgroup. -/
def rootBase : G.rootSystem.Base :=
  borelRootBase G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive

/-- The Weyl group of the chosen maximal torus. -/
abbrev weylGroup := G.rootSystem.weylGroup

/-- The longest element of the Weyl group for the chosen positive roots. -/
def longestElement : G.weylGroup := longestWeylElement G.rootBase

end ReductiveGroupData
