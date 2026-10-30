import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import TauCeti.Algebra.Lie.Sl2.Standard

/-!
# Lie homomorphisms of simple-root pairs

The chosen positive and negative additive root parameters determine an injective
homomorphism from the matrix Lie algebra `sl₂` to the tangent Lie algebra.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open LieAlgebra Module

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem simpleRoot_triple (i : G.rootBase.support) :
    IsSl2Triple
      ⁅gaAffineGroupTangent (G.simpleRootMap i),
        gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆
      (gaAffineGroupTangent (G.simpleRootMap i))
      (gaAffineGroupTangent (G.negativeSimpleRootMap i)) :=
  (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)).isSl2Triple

/-- The matrix Lie algebra `sl₂` maps to the tangent algebra through the chosen
simple-root pair. -/
def simpleSl2LieHom (i : G.rootBase.support) :
    SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ G.tangent :=
  TauCeti.lieHomOfSl2Basis (TauCeti.slFinTwoBasis K)
    (TauCeti.lie_slFinTwoBasis_zero_one K)
    (TauCeti.lie_slFinTwoBasis_two_zero K)
    (TauCeti.lie_slFinTwoBasis_two_one K)
    (gaAffineGroupTangent (G.simpleRootMap i))
    (gaAffineGroupTangent (G.negativeSimpleRootMap i))
    ⁅gaAffineGroupTangent (G.simpleRootMap i),
      gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆
    rfl ((simpleRoot_triple G i).lie_h_e_smul K)
    ((simpleRoot_triple G i).lie_lie_smul_f K)

/-- The standard `sl₂` basis maps to the two chosen root tangents and their bracket. -/
theorem simpleSl2LieHom_basis (i : G.rootBase.support) (j : Fin 3) :
    G.simpleSl2LieHom i (TauCeti.slFinTwoBasis K j) =
      ![gaAffineGroupTangent (G.simpleRootMap i),
        gaAffineGroupTangent (G.negativeSimpleRootMap i),
        ⁅gaAffineGroupTangent (G.simpleRootMap i),
          gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆] j :=
  TauCeti.lieHomOfSl2Basis_apply ..

/-- The simple-root map from the matrix Lie algebra `sl₂` is injective. -/
theorem simpleSl2LieHom_injective (i : G.rootBase.support) :
    Function.Injective (G.simpleSl2LieHom i) := by
  intro x y hxy
  apply (TauCeti.slFinTwoBasis K).repr.injective
  apply DFunLike.coe_injective
  apply (TauCeti.linearIndependent_isSl2Triple
    (simpleRoot_triple G i)).fintypeLinearCombination_injective
  have hx := congrArg (G.simpleSl2LieHom i) ((TauCeti.slFinTwoBasis K).sum_repr x)
  have hy := congrArg (G.simpleSl2LieHom i) ((TauCeti.slFinTwoBasis K).sum_repr y)
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply, simpleSl2LieHom_basis] at hx hy
  exact hx.trans (hxy.trans hy.symm)

end ReductiveGroups.ReductiveGroupData
