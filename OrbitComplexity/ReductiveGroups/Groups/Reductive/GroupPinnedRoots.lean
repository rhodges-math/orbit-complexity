import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupChevalley
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleScaling
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Lie

/-! # Conjugation and simple-root normalization of Chevalley systems -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra LieModule LieAlgebra.IsKilling TauCeti

universe u v
variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

private theorem pair_scalars {x : Weight K H L → L} (hx : IsSl2System x)
    (α : Weight K H L) (hα : α.IsNonZero) (e f : L)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α : Weight K H L))
    (hef : ⁅e, f⁆ = (coroot α : L)) :
    ∃ c : Kˣ, e = (c : K) • x α ∧ f = (c : K)⁻¹ • x (-α) := by
  have he' : e ∈ K ∙ x α := by
    rw [← hx.toSubmodule_rootSpace_eq_span α hα]
    exact he
  have hf' : f ∈ K ∙ x (-α) := by
    rw [← hx.toSubmodule_rootSpace_eq_span (-α) hα.neg]
    exact hf
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he'
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hf'
  have hcoroot : (coroot α : L) ≠ 0 := by
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero, coroot_eq_zero_iff] using hα
  have hab : a * b = 1 := by
    apply (smul_left_injective K hcoroot)
    change (a * b) • (coroot α : L) = (1 : K) • (coroot α : L)
    rw [one_smul, ← hx.lie_neg α hα, ← smul_smul, ← lie_smul, ← smul_lie,
      ha, hb, hef]
    exact (hx.lie_neg α hα).symm
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  refine ⟨Units.mk0 a ha0, ha.symm, ?_⟩
  have hb' : b = a⁻¹ := by
    apply mul_left_cancel₀ ha0
    rw [hab, mul_inv_cancel₀ ha0]
  simpa only [Units.val_mk0, hb'] using hb.symm

/-- Conjugating a Chevalley system transports both its vectors and involution. -/
theorem chevalleySystem_conjugate {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}
    (hx : IsChevalleySystem ω x) (σ : L ≃ₗ⁅K⁆ L)
    (hσ : H.map σ.toLieHom = H) :
    IsChevalleySystem ((σ.symm.trans ω).trans σ)
      (fun α => σ (x ((weightPerm σ hσ).symm α))) := by
  refine ⟨hx.toIsSl2System.map σ hσ, ?_⟩
  intro α
  change σ (ω (σ.symm (σ (x ((weightPerm σ hσ).symm α))))) = _
  rw [σ.symm_apply_apply, hx.map_root, map_neg, weightPerm_symm_neg]

namespace ReductiveGroupData

variable [IsAlgClosed K] (G : ReductiveGroupData K)

private theorem root_differential (r : G.rootIndex) (t : G.torusTangent) :
    G.rootSystem.root r (centerQuotientCartanMap G.torusTangent t) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) t := by
  have h := ReductiveCharacterCenterQuotientRootEquiv.apply_map
    G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero
    G.reductive (G.characterRootEquiv.symm r) t
  change G.rootSystem.root (G.characterRootEquiv (G.characterRootEquiv.symm r))
    (centerQuotientCartanMap G.torusTangent t) = _ at h
  simpa only [rootCharacter, Equiv.apply_symm_apply] using h

private theorem quotient_root_mem (r : G.rootIndex) (d : G.tangent)
    (hd : d ∈ G.rootWeightSpace r) :
    centerQuotientLieHom (K := K) d ∈ rootSpace G.cartan (G.rootSystem.root r) := by
  have hf : (fun h : G.torusTangent =>
      G.rootSystem.root r (centerQuotientCartanMap G.torusTangent h)) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) :=
    funext (root_differential G r)
  change d ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r) at hd
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective,
    ← hf] at hd
  exact (centerQuotientRootSpaceMap G.torusTangent (G.rootSystem.root r) ⟨d, hd⟩).property

private theorem simple_pair_bracket (i : G.rootBase.support) :
    ⁅centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.simpleRootMap i)),
      centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.negativeSimpleRootMap i))⁆ =
        (coroot i.val.val : G.centerQuotient) := by
  let alpha := G.characterRootEquiv.symm i.val
  have hp := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive alpha
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
  rw [← LieHom.map_lie]
  have hq := centerQuotient_sl2_h_eq_coroot G.torusTangent chi.val chi.property
    hp.isSl2Triple he hf hp.bracket_mem
  change _ = (coroot (G.characterRootEquiv alpha).val : G.centerQuotient) at hq
  simpa only [simpleRootMap, negativeSimpleRootMap, alpha, Equiv.apply_symm_apply] using hq

/-- A Chevalley system can agree with both fixed simple-root tangents in the center quotient. -/
theorem exists_pinnedChevalleySystem :
    ∃ (ω : G.centerQuotient ≃ₗ⁅K⁆ G.centerQuotient)
      (x : Weight K G.cartan G.centerQuotient → G.centerQuotient),
      IsChevalleySystem ω x ∧ ∀ i : G.rootBase.support,
        x i.val.val = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.simpleRootMap i)) ∧
        x (-i.val.val) = centerQuotientLieHom (K := K)
          (gaAffineGroupTangent (G.negativeSimpleRootMap i)) := by
  obtain ⟨ω, x, hx⟩ := G.exists_chevalleySystem
  have hpair (i : G.rootBase.support) :
      ∃ c : Kˣ,
        centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.simpleRootMap i)) =
          (c : K) • x i.val.val ∧
        centerQuotientLieHom (K := K) (gaAffineGroupTangent (G.negativeSimpleRootMap i)) =
          (c : K)⁻¹ • x (-i.val.val) := by
    apply pair_scalars hx.toIsSl2System i.val.val
      (LieSubalgebra.isNonZero_coe_root i.val)
    · exact quotient_root_mem G i.val _ (G.simpleRootMap_tangent_mem i)
    · exact quotient_root_mem G (-i.val) _ (G.negativeRootMap_tangent_mem i)
    · exact simple_pair_bracket G i
  choose c hc using hpair
  obtain ⟨t, ht, hi⟩ := G.exists_simple_quotient_scaling c
  let σ := centerQuotientEquiv (affineGroupAdjointLieEquiv (t : G.points))
  have hσ : G.cartan.map σ.toLieHom = G.cartan := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change σ z ∈ G.cartan
      rw [ht ⟨z, hz⟩]
      exact hz
    · intro hy
      exact ⟨y, hy, ht ⟨y, hy⟩⟩
  have hp : ∀ α : Weight K G.cartan G.centerQuotient,
      (weightPerm σ hσ).symm α = α := by
    intro α
    ext h
    rw [weightPerm_symm_apply_apply]
    exact congrArg α (Subtype.ext (ht h))
  refine ⟨(σ.symm.trans ω).trans σ, fun α => σ (x α), ?_, ?_⟩
  · simpa only [hp] using chevalleySystem_conjugate hx σ hσ
  · intro i
    exact ⟨((hi i).1 _ (hx.toIsSl2System.mem_rootSpace i.val.val)).trans (hc i).1.symm,
      ((hi i).2 _ (hx.toIsSl2System.mem_rootSpace (-i.val.val))).trans (hc i).2.symm⟩

end ReductiveGroupData

end ReductiveGroups
