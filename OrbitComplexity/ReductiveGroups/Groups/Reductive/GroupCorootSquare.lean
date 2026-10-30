import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCoroots
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflectionTransport

/-! # The exact simple representative square and full coroot contract -/

noncomputable section

namespace ReductiveGroups.Coroot

section

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The full-character Cartan functional has the existing integral root pairing. -/
private theorem simpleCartan_root_pairing (i : G.rootBase.support) (r : G.rootIndex) :
    characterDifferentialOnImage G.torusSplit G.split_surjective
      (G.rootCharacter r) (simpleCartan G i) =
        (G.rootSystem.pairingIn ℤ r i.val : K) := by
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
  rw [← G.rootSystem.algebraMap_pairingIn ℤ r i.val] at hc
  exact hc

/-- The integral functional restricts to the prescribed Cartan integers. -/
private theorem simpleCorootFunctional_root (i : G.rootBase.support) (r : G.rootIndex) :
    simpleCorootFunctional G i (G.rootCharacter r).toAdd =
      G.rootSystem.pairingIn ℤ r i.val := by
  apply Int.cast_injective (α := K)
  rw [simpleCorootFunctional_cast]
  exact simpleCartan_root_pairing G i r

end

section

open TauCeti Module WithConv

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The representative square is the simple coroot evaluated at minus one. -/
theorem simple_square_eq_coroot (i : G.rootBase.support) :
    (G.reflectionPoint i.val) ^ 2 = simpleCorootPoint G i (-1) := by
  have hp := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)
  have hT : (G.reflectionPoint i.val) ^ 2 ∈ G.torusPoints :=
    hp.rootReflectionPoint_sq_mem_torusPoints G.torusIdeal G.split_surjective
      G.split_eq_zero
  obtain ⟨z, hz⟩ := (mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero _).mp hT
  have he : z = simpleCorootTorusPoint G i (-1) := by
    apply (DiagonalizableGroup.pointsMulEquiv
      (R := K) (A := K) (G := G.characters)).injective
    apply MonoidHom.ext
    intro chi
    apply Units.ext
    change z.ofConv (MonoidAlgebra.single chi 1) =
      (simpleCorootTorusPoint G i (-1)).ofConv (MonoidAlgebra.single chi 1)
    rw [simpleCorootTorusPoint_eval]
    rw [Units.val_zpow_eq_zpow_val, Units.coe_neg_one]
    exact square_character_value G i z hz chi
  exact hz.trans (congrArg (AlgHom.mapDomain G.torusSplit) he)

end

section

open TauCeti WithConv

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The exact simple coroot exists on the full character lattice and has the required square. -/
theorem simple_coroot_exists (i : G.rootBase.support) :
    ∃ l : (G.torusIndex →₀ ℤ) →+ ℤ,
    ∃ c : G.characters →* Multiplicative ℤ,
    ∃ phi : G.coordinateAlgebra →ₐc[K] MonoidAlgebra K (Multiplicative ℤ),
      (∀ a, (l a : K) = characterDifferentialOnImage G.torusSplit G.split_surjective
        (Multiplicative.ofAdd a) (simpleCartan G i)) ∧
      (∀ chi, c chi = Multiplicative.ofAdd (l chi.toAdd)) ∧
      phi = (MonoidAlgebra.mapDomainBialgHom K c).comp G.torusSplit ∧
      (∀ r, l (G.rootCharacter r).toAdd = G.rootSystem.pairingIn ℤ r i.val) ∧
      derivationComp (B := K) phi (multiplicativeTangent (K := K)) =
        (simpleCartan G i : G.tangent) ∧
      (G.reflectionPoint i.val) ^ 2 = AlgHom.mapDomain phi
        ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ (-1))) := by
  refine ⟨simpleCorootFunctional G i, simpleCorootCharacter G i, simpleCorootMap G i,
    simpleCorootFunctional_cast G i, (fun chi => rfl), rfl,
    simpleCorootFunctional_root G i, simpleCorootMap_differential G i, ?_⟩
  exact (simple_square_eq_coroot G i).trans (simpleCorootPoint_map G i (-1))

end

end ReductiveGroups.Coroot
