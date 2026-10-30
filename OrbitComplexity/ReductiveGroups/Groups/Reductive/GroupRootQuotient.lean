import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData

/-! # Root-character spaces and the tangent center quotient -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open LieAlgebra LieModule

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem root_differential (r : G.rootIndex) (t : G.torusTangent) :
    G.rootSystem.root r (centerQuotientCartanMap G.torusTangent t) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) t := by
  have h := ReductiveCharacterCenterQuotientRootEquiv.apply_map
    G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero
    G.reductive (G.characterRootEquiv.symm r) t
  change G.rootSystem.root (G.characterRootEquiv (G.characterRootEquiv.symm r))
    (centerQuotientCartanMap G.torusTangent t) = _ at h
  simpa only [rootCharacter, Equiv.apply_symm_apply] using h

private theorem rootSpace_eq (r : G.rootIndex) :
    G.rootWeightSpace r = (rootSpace G.torusTangent (fun h =>
      G.rootSystem.root r (centerQuotientCartanMap G.torusTangent h))).toSubmodule := by
  ext d
  change d ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r) ↔ _
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective]
  have hf : (fun h : G.torusTangent =>
      G.rootSystem.root r (centerQuotientCartanMap G.torusTangent h)) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) :=
    funext (root_differential G r)
  rw [hf]

/-- A root-character space maps isomorphically to its root space in the center quotient. -/
def rootWeightQuotientEquiv (r : G.rootIndex) :
    G.rootWeightSpace r ≃ₗ[K] rootSpace G.cartan (G.rootSystem.root r) :=
  (LinearEquiv.ofEq _ _ (rootSpace_eq G r)).trans
    (centerQuotientRootSpaceEquiv G.torusTangent (G.rootSystem.root r)
      (LieSubalgebra.isNonZero_coe_root r))

/-- The root-space equivalence is induced by the tangent center quotient map. -/
theorem rootWeightQuotientEquiv_apply (r : G.rootIndex) (x : G.rootWeightSpace r) :
    (G.rootWeightQuotientEquiv r x : G.centerQuotient) =
      centerQuotientLieHom (K := K) (x : G.tangent) := rfl

end ReductiveGroups.ReductiveGroupData
