import OrbitComplexity.ReductiveGroups.Lie.Roots.Sl2WeylSquare
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Lie
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflectionTransport

/-! # The exact square action of the fixed simple representatives -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The Cartan element of the chosen simple pair acts by the integral root pairing. -/
private theorem simplePair_cartan_weight (i : G.rootBase.support) (r : G.rootIndex)
    (v : G.tangent) (hv : v ∈ G.rootWeightSpace r) :
    ⁅⁅gaAffineGroupTangent (G.simpleRootMap i),
        gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆, v⁆ =
      (G.rootSystem.pairingIn ℤ r i.val : K) • v := by
  let alpha := G.characterRootEquiv.symm i.val
  have hp := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive alpha
  let h : G.torusTangent := ⟨_, hp.bracket_mem⟩
  let chi := nonidentityCharacterLieWeightEquiv G.torusSplit G.split_surjective alpha
  have hchi : (chi.val : G.torusTangent → K) =
      characterDifferentialOnImage G.torusSplit G.split_surjective alpha.val := by
    funext t
    exact nonidentityCharacterLieWeightEquiv_apply G.torusSplit
      G.split_surjective alpha t
  have he : gaAffineGroupTangent (G.simpleRootMap i) ∈
      rootSpace G.torusTangent chi.val := by
    have hm := hp.tangent_mem
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective,
      ← hchi] at hm
    exact hm
  have hf : gaAffineGroupTangent (G.negativeSimpleRootMap i) ∈
      rootSpace G.torusTangent (-(chi.val : G.torusTangent → K)) := by
    have hm := hp.partner_tangent_mem
    have hneg : (characterDifferentialOnImage G.torusSplit G.split_surjective
        alpha.val⁻¹ : G.torusTangent → K) = -(chi.val : G.torusTangent → K) := by
      rw [characterDifferentialOnImage_inv, hchi]
      rfl
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective,
      hneg] at hm
    exact hm
  have hqh : centerQuotientCartanMap G.torusTangent h =
      coroot (G.characterRootEquiv alpha).val := by
    apply Subtype.ext
    exact centerQuotient_sl2_h_eq_coroot G.torusTangent chi.val chi.property
      hp.isSl2Triple he hf hp.bracket_mem
  have hc : characterDifferentialOnImage G.torusSplit G.split_surjective
      (G.rootCharacter r) h = G.rootSystem.pairing r i.val := by
    have hm := ReductiveCharacterCenterQuotientRootEquiv.apply_map
      G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective
      G.split_eq_zero G.reductive (G.characterRootEquiv.symm r) h
    change (G.characterRootEquiv (G.characterRootEquiv.symm r)).val
      (centerQuotientCartanMap G.torusTangent h) = _ at hm
    rw [G.characterRootEquiv.apply_symm_apply, hqh,
      show G.characterRootEquiv alpha = i.val from G.characterRootEquiv.apply_symm_apply _]
      at hm
    exact hm.symm
  have hw := RootRankOneSl2Pair.eq_smul_of_mem_characterWeight
    G.torusSplit G.split_surjective (G.rootCharacter r) v hv h
  rw [hc, ← G.rootSystem.algebraMap_pairingIn ℤ r i.val] at hw
  exact hw


omit [IsAlgClosed K] in
private theorem ga_adjoint_exp
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) (t : K) (v : G.tangent) :
    let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
    affineGroupAdjointRepresentation (gaParameterPoint x t) v =
      (IsNilpotent.exp
        (ad K G.tangent (t • gaAffineGroupTangent x))) v := by
  let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
  change affineGroupAdjointRepresentation
    (gaAffineGroupPoints x (Multiplicative.ofAdd t)) v = _
  rw [affineGroupAdjointRepresentation_apply, gaAffineGroup_adjoint_eq_exponential]
  unfold nilpotentLieAdjointExponential
  rw [LieDerivation.exp_map_apply]
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply]
  rfl

/-- The fixed simple representative squares to the parity of each integral root weight. -/
theorem simpleReflection_square_weight (i : G.rootBase.support) (r : G.rootIndex)
    (v : G.tangent) (hv : v ∈ G.rootWeightSpace r) :
    affineGroupAdjointRepresentation ((G.reflectionPoint i.val) ^ 2) v =
      (-1 : K) ^ G.rootSystem.pairingIn ℤ r i.val • v := by
  let : Module ℚ G.tangent := Module.compHom G.tangent (algebraMap ℚ K)
  let : LieRingModule (SpecialLinear.sl (Fin 2) K) G.tangent :=
    LieRingModule.compLieHom G.tangent (G.simpleSl2LieHom i)
  let : LieModule K (SpecialLinear.sl (Fin 2) K) G.tangent :=
    LieModule.compLieHom G.tangent (G.simpleSl2LieHom i)
  let E := ad K G.tangent (gaAffineGroupTangent (G.simpleRootMap i))
  let F := ad K G.tangent (gaAffineGroupTangent (G.negativeSimpleRootMap i))
  let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
  have he : toEnd K (SpecialLinear.sl (Fin 2) K) G.tangent
      (TauCeti.slFinTwoBasis K 0) = E := by
    apply LinearMap.ext
    intro z
    change ⁅G.simpleSl2LieHom i (TauCeti.slFinTwoBasis K 0), z⁆ = _
    rw [G.simpleSl2LieHom_basis]
    rfl
  have hf : toEnd K (SpecialLinear.sl (Fin 2) K) G.tangent
      (TauCeti.slFinTwoBasis K 1) = F := by
    apply LinearMap.ext
    intro z
    change ⁅G.simpleSl2LieHom i (TauCeti.slFinTwoBasis K 1), z⁆ = _
    rw [G.simpleSl2LieHom_basis]
    rfl
  have hh : ⁅TauCeti.slFinTwoBasis K 2, v⁆ =
      (G.rootSystem.pairingIn ℤ r i.val : K) • v := by
    change ⁅G.simpleSl2LieHom i (TauCeti.slFinTwoBasis K 2), v⁆ = _
    rw [G.simpleSl2LieHom_basis]
    exact G.simplePair_cartan_weight i r v hv
  have sq := ReductiveGroups.Sl2Square.square_on_weight
    (M := G.tangent) (by rw [he]; exact gaAffineGroupTangent_ad_nilpotent _)
    (by rw [hf]; exact gaAffineGroupTangent_ad_nilpotent _)
    (G.rootSystem.pairingIn ℤ r i.val) v hh
  dsimp only at sq
  rw [he, hf] at sq
  have hW (z : G.tangent) :
      affineGroupAdjointRepresentation (G.reflectionPoint i.val) z = W z := by
    change affineGroupAdjointRepresentation
      (gaParameterPoint (G.simpleRootMap i) 1 *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1) *
        gaParameterPoint (G.simpleRootMap i) 1) z = W z
    have hminus : ad K G.tangent
        ((-1 : K) • gaAffineGroupTangent (G.negativeSimpleRootMap i)) = -F := by
      exact (congrArg (ad K G.tangent)
        (neg_one_smul K (gaAffineGroupTangent (G.negativeSimpleRootMap i)))).trans
        ((ad K G.tangent).map_neg _)
    simp only [map_mul, Module.End.mul_apply, ga_adjoint_exp G, one_smul]
    rw [hminus]
    rfl
  rw [map_pow, pow_two, Module.End.mul_apply, hW, hW]
  exact sq


end ReductiveGroups.ReductiveGroupData
