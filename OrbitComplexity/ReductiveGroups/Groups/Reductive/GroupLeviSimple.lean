import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots

/-!
# Selected simple-root points in the Levi subgroup

Both members of a selected simple-root pair commute with the common character
kernel. Their rank-one product represents the corresponding simple reflection.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A selected positive simple-root parameter lies in the standard Levi point group. -/
theorem simpleRootPoint_mem_levi (I : Set G.rootBase.support)
    (i : G.rootBase.support) (hi : i ∈ I) (c : K) :
    gaParameterPoint (G.simpleRootMap i) c ∈ G.leviPoints I := by
  rintro _ ⟨z, rfl, hz⟩
  have he := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter i.val) z (G.simpleRootMap i) (G.simpleRootMap_tangent_mem i) c
  have hzi : z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) = 1 := hz i hi
  have hc : AlgHom.mapDomain G.torusSplit z * gaParameterPoint (G.simpleRootMap i) c *
      (AlgHom.mapDomain G.torusSplit z)⁻¹ = gaParameterPoint (G.simpleRootMap i) c := by
    simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hzi, one_mul] using he
  exact (mul_inv_eq_iff_eq_mul).mp hc

/-- A selected negative simple-root parameter lies in the standard Levi point group. -/
theorem negativeRootPoint_mem_levi (I : Set G.rootBase.support)
    (i : G.rootBase.support) (hi : i ∈ I) (c : K) :
    gaParameterPoint (G.negativeSimpleRootMap i) c ∈ G.leviPoints I := by
  rintro _ ⟨z, rfl, hz⟩
  have hweight := (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)).partner_tangent_mem
  have he := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter i.val)⁻¹ z (G.negativeSimpleRootMap i) hweight c
  have hzi : z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) = 1 := hz i hi
  have hzinv : z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val)⁻¹ 1) = 1 := by
    rw [torusPoint_character_inv, hzi, inv_one]
  have hc : AlgHom.mapDomain G.torusSplit z *
      gaParameterPoint (G.negativeSimpleRootMap i) c *
      (AlgHom.mapDomain G.torusSplit z)⁻¹ = gaParameterPoint (G.negativeSimpleRootMap i) c := by
    simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hzinv, one_mul] using he
  exact (mul_inv_eq_iff_eq_mul).mp hc

/-- Each selected simple reflection representative lies in the standard Levi point group. -/
theorem reflectionPoint_mem_levi (I : Set G.rootBase.support)
    (i : G.rootBase.support) (hi : i ∈ I) : G.reflectionPoint i.val ∈ G.leviPoints I := by
  change gaParameterPoint (G.simpleRootMap i) 1 *
    gaParameterPoint (G.negativeSimpleRootMap i) (-1) *
    gaParameterPoint (G.simpleRootMap i) 1 ∈ G.leviPoints I
  exact (G.leviPoints I).mul_mem
    ((G.leviPoints I).mul_mem (G.simpleRootPoint_mem_levi I i hi 1)
      (G.negativeRootPoint_mem_levi I i hi (-1))) (G.simpleRootPoint_mem_levi I i hi 1)

end ReductiveGroups.ReductiveGroupData
