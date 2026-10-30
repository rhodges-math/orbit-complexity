import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPinnedReflections
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootQuotient

/-! # Signed action of simple representatives on pinned root vectors -/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open LieAlgebra LieAlgebra.IsKilling LieModule TauCeti

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem simple_cartan (i : G.rootBase.support) :
    G.cartan.map (centerQuotientEquiv
      (affineGroupAdjointLieEquiv (G.reflectionPoint i.val))).toLieHom = G.cartan := by
  have hp := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv⟩ := centerQuotientCartanMap_surjective G.torusTangent ⟨z, hz⟩
    have hv' := congrArg Subtype.val hv
    change centerQuotientLieHom (K := K) (v : G.tangent) = z at hv'
    change centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) z ∈
      G.cartan
    rw [← hv', centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply]
    have hm : affineGroupAdjointRepresentation (G.reflectionPoint i.val)
        (v : G.tangent) ∈ G.torusTangent :=
      hp.adjoint_rootReflectionPoint_mem G.split_surjective v
    exact (centerQuotientCartanMap G.torusTangent ⟨_, hm⟩).property
  · intro hy
    obtain ⟨v, hv⟩ := centerQuotientCartanMap_surjective G.torusTangent ⟨y, hy⟩
    obtain ⟨w, hw⟩ := hp.adjoint_rootReflectionPoint_onto G.split_surjective v
    refine ⟨centerQuotientLieHom (K := K) (w : G.tangent),
      (centerQuotientCartanMap G.torusTangent w).property, ?_⟩
    change centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val))
      (centerQuotientLieHom (K := K) (w : G.tangent)) = y
    rw [centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply]
    have hw' : affineGroupAdjointRepresentation (G.reflectionPoint i.val)
        (w : G.tangent) = (v : G.tangent) := hw
    rw [hw']
    exact congrArg Subtype.val hv

private theorem quotient_root_transport (p : G.points) (τ : Equiv.Perm G.rootIndex)
    (hp : G.rootPointTransport p τ) (r : G.rootIndex) (v : G.centerQuotient)
    (hv : v ∈ rootSpace G.cartan (G.rootSystem.root r)) :
    centerQuotientEquiv (affineGroupAdjointLieEquiv p) v ∈
      rootSpace G.cartan (G.rootSystem.root (τ r)) := by
  obtain ⟨z, hz⟩ := (G.rootWeightQuotientEquiv r).surjective ⟨v, hv⟩
  have hz' : centerQuotientLieHom (K := K) (z : G.tangent) = v :=
    (G.rootWeightQuotientEquiv_apply r z).symm.trans (congrArg Subtype.val hz)
  rw [← hz', centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply]
  have hm : affineGroupAdjointRepresentation p (z : G.tangent) ∈ G.rootWeightSpace (τ r) := by
    rw [← hp r]
    exact ⟨z, z.property, rfl⟩
  exact (G.rootWeightQuotientEquiv (τ r) ⟨_, hm⟩).property

private theorem simple_weightPerm {x : Weight K G.cartan G.centerQuotient → G.centerQuotient}
    (hx : IsSl2System x) (i : G.rootBase.support) (r : G.rootIndex) :
    weightPerm (centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)))
      (simple_cartan G i) r.val = (G.rootSystem.reflectionPerm i.val r).val := by
  let σ := centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val))
  have hfirst := map_mem_rootSpace_weightPerm σ (simple_cartan G i) (hx.mem_rootSpace r.val)
  have hsecond := quotient_root_transport G (G.reflectionPoint i.val)
    (G.rootSystem.reflectionPerm i.val) (G.isBruhatSystem.weyl.transport_reflection i.val)
    r (x r.val) (hx.mem_rootSpace r.val)
  have hne : σ (x r.val) ≠ 0 := fun h =>
    hx.ne_zero r.val (LieSubalgebra.isNonZero_coe_root r)
      (σ.injective (h.trans (map_zero σ).symm))
  ext h
  apply smul_left_injective K hne
  exact (lie_eq_smul_of_mem_rootSpace hfirst h).symm.trans
    (lie_eq_smul_of_mem_rootSpace hsecond h)

/-- One family matching the chosen simple parameters has signed simple-reflection transport. -/
theorem exists_simpleRootSigns :
    ∃ (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
      (x : Weight K G.cartan G.centerQuotient → G.centerQuotient),
      IsChevalleySystem ω x ∧
      (∀ i : G.rootBase.support,
        x i.val.val = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.simpleRootMap i)) ∧
        x (-i.val.val) = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.negativeSimpleRootMap i))) ∧
      ∀ (i : G.rootBase.support) (r : G.rootIndex),
        centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) (x r.val) =
          x (G.rootSystem.reflectionPerm i.val r).val ∨
        centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)) (x r.val) =
          -x (G.rootSystem.reflectionPerm i.val r).val := by
  obtain ⟨ω, x, hx, hi, hcomm⟩ := G.exists_reflectionChevalleySystem
  refine ⟨ω, x, hx, hi, ?_⟩
  intro i r
  have h := hx.aut_apply_eq_or_eq_neg
    (centerQuotientEquiv (affineGroupAdjointLieEquiv (G.reflectionPoint i.val)))
    (simple_cartan G i) (hcomm i) r.val
  rwa [simple_weightPerm G hx.toIsSl2System i r] at h

end ReductiveGroups.ReductiveGroupData
