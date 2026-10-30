import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootDecomposition
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientAutomorphisms

/-! # Simultaneous simple-root scaling and its center quotient action -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti WithConv LieAlgebra
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Arbitrary nonzero simple-character values give exact positive and negative scalings. -/
theorem exists_simple_scaling (c : G.rootBase.support → Kˣ) :
    ∃ t : G.torusPoints,
    ∃ z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K),
      (t : G.points) = AlgHom.mapDomain G.torusSplit z ∧
      (∀ i, z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) = c i) ∧
      ∀ (i : G.rootBase.support) (a : K),
        (t : G.points) * gaParameterPoint (G.simpleRootMap i) a * (t : G.points)⁻¹ =
          gaParameterPoint (G.simpleRootMap i) ((c i : K) * a) ∧
        (t : G.points) * gaParameterPoint (G.negativeSimpleRootMap i) a *
            (t : G.points)⁻¹ =
          gaParameterPoint (G.negativeSimpleRootMap i) ((c i : K)⁻¹ * a) := by
  obtain ⟨z, hz⟩ := exists_torusPoint_character_values (K := K)
    (fun i : G.rootBase.support => G.rootCharacter i.val) G.rootCharacter_independent c
  let t : G.torusPoints := ⟨AlgHom.mapDomain G.torusSplit z,
    mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective G.split_eq_zero z⟩
  refine ⟨t, z, rfl, hz, fun i a => ⟨?_, ?_⟩⟩
  · have h := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
      (G.rootCharacter i.val) z (G.simpleRootMap i) (G.simpleRootMap_tangent_mem i) a
    simpa only [t, gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hz i] using h
  · have hw := (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
      G.torusSplit G.split_surjective G.split_eq_zero G.reductive
      (G.characterRootEquiv.symm i.val)).partner_tangent_mem
    have h := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
      (G.rootCharacter i.val)⁻¹ z (G.negativeSimpleRootMap i) hw a
    rw [torusPoint_character_inv, hz i] at h
    simpa only [t, gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] using h

private theorem negative_character (r : G.rootIndex) :
    G.rootCharacter (-r) = (G.rootCharacter r)⁻¹ := by
  have h : G.rootSystem.rootSpanMem ℤ (-r) = -G.rootSystem.rootSpanMem ℤ r := by
    apply Subtype.ext
    simp
  have hm := congrArg G.rootCharacterMap h
  rw [map_neg, G.rootCharacterMap_root, G.rootCharacterMap_root] at hm
  exact hm

/-- One torus point fixes the torus tangent and scales every simple-root weight vector. -/
theorem exists_simple_adjoint (c : G.rootBase.support → Kˣ) :
    ∃ t : G.torusPoints,
      (∀ h : G.torusTangent, affineGroupAdjointRepresentation (t : G.points)
        (h : G.tangent) = (h : G.tangent)) ∧
      ∀ i : G.rootBase.support,
        (∀ d : G.tangent, d ∈ G.rootWeightSpace i.val →
          affineGroupAdjointRepresentation (t : G.points) d = (c i : K) • d) ∧
        (∀ d : G.tangent, d ∈ G.rootWeightSpace (-i.val) →
          affineGroupAdjointRepresentation (t : G.points) d = (c i : K)⁻¹ • d) := by
  obtain ⟨t, z, ht, hz, _⟩ := G.exists_simple_scaling c
  refine ⟨t, ?_, fun i => ⟨?_, ?_⟩⟩
  · intro h
    have hh : (h : G.tangent) ∈ affineGroupCharacterWeightSpace G.torusSplit 1 := by
      rw [G.identityWeightSpace_eq_torus]
      exact h.property
    rw [ht, AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit 1 z _ hh]
    simp only [← MonoidAlgebra.one_def, map_one, one_smul]
  · intro d hd
    rw [ht, AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter i.val) z d hd, hz i]
  · intro d hd
    change d ∈ affineGroupCharacterWeightSpace G.torusSplit
      (G.rootCharacter (-i.val)) at hd
    rw [negative_character] at hd
    rw [ht, AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter i.val)⁻¹ z d hd, torusPoint_character_inv, hz i]

private theorem root_differential (r : G.rootIndex) (t : G.torusTangent) :
    G.rootSystem.root r (centerQuotientCartanMap G.torusTangent t) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) t := by
  have h := ReductiveCharacterCenterQuotientRootEquiv.apply_map
    G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero
    G.reductive (G.characterRootEquiv.symm r) t
  change G.rootSystem.root (G.characterRootEquiv (G.characterRootEquiv.symm r))
    (centerQuotientCartanMap G.torusTangent t) = _ at h
  simpa only [rootCharacter, Equiv.apply_symm_apply] using h

private theorem weight_lift (r : G.rootIndex)
    (x : rootSpace G.cartan (G.rootSystem.root r)) :
    ∃ d : G.tangent, d ∈ G.rootWeightSpace r ∧
      centerQuotientLieHom (K := K) d = (x : G.centerQuotient) := by
  obtain ⟨d, hd⟩ := centerQuotientRootSpaceMap_surjective G.torusTangent
    (G.rootSystem.root r) x
  refine ⟨d, ?_, congrArg Subtype.val hd⟩
  change (d : G.tangent) ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective]
  have hf : (fun h : G.torusTangent =>
      G.rootSystem.root r (centerQuotientCartanMap G.torusTangent h)) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) :=
    funext (root_differential G r)
  rw [← hf]
  exact d.property

/-- Prescribed simple-root scalars act on every quotient root vector and fix its Cartan. -/
theorem exists_simple_quotient_scaling (c : G.rootBase.support → Kˣ) :
    ∃ t : G.torusPoints,
      (∀ h : G.cartan, centerQuotientEquiv (affineGroupAdjointLieEquiv (t : G.points))
        (h : G.centerQuotient) = (h : G.centerQuotient)) ∧
      ∀ i : G.rootBase.support,
        (∀ x : G.centerQuotient, x ∈ rootSpace G.cartan (G.rootSystem.root i.val) →
          centerQuotientEquiv (affineGroupAdjointLieEquiv (t : G.points)) x =
            (c i : K) • x) ∧
        (∀ x : G.centerQuotient, x ∈ rootSpace G.cartan (G.rootSystem.root (-i.val)) →
          centerQuotientEquiv (affineGroupAdjointLieEquiv (t : G.points)) x =
            (c i : K)⁻¹ • x) := by
  obtain ⟨t, ht, hi⟩ := G.exists_simple_adjoint c
  refine ⟨t, ?_, fun i => ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨v, hv⟩ := centerQuotientCartanMap_surjective G.torusTangent h
    have hv' := congrArg Subtype.val hv
    change centerQuotientLieHom (K := K) (v : G.tangent) = (h : G.centerQuotient) at hv'
    rw [← hv', centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply, ht v]
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := weight_lift G i.val ⟨x, hx⟩
    change centerQuotientLieHom (K := K) d = x at hdx
    rw [← hdx, centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply,
      (hi i).1 d hd, map_smul]
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := weight_lift G (-i.val) ⟨x, hx⟩
    change centerQuotientLieHom (K := K) d = x at hdx
    rw [← hdx, centerQuotientEquiv_apply, affineGroupAdjointLieEquiv_apply,
      (hi i).2 d hd, map_smul]

end ReductiveGroups.ReductiveGroupData
