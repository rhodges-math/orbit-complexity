import OrbitComplexity.ReductiveGroups.Groups.Cells.SchubertCellAbstract
import OrbitComplexity.ReductiveGroups.Groups.Cells.SchubertCellDefs
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubsetGroup
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSubsetTorus
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateBasis
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneSweepClosed
import OrbitComplexity.ReductiveGroups.Groups.Cells.RootBorelPoints

/-! # Rank-one Bruhat data of a reductive group -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

-- The conjugation identity transports the chosen root-sl₂ pair through the Cartan
-- character spaces and the center quotient, with nested root-space coercions.
set_option maxHeartbeats 1000000 in
/-- For a simple root `i` and a Borel root character `k` whose root is not `i`,
`n_i⁻¹ z(c) n_i` is a Borel point for every root subgroup `z` of `k`: the
simple reflection permutes the positive roots other than `α_i`. -/
theorem SchubertCellRankOne.reflectionPoint_conj_ga_mem_borel
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let b := borelRootBase I J hJI hI hJ π hπ hker hB
    ∀ (i : b.support) (k : borelRootCharacterIndex J π),
      E (borelRootCharacterOccurring J π k) ≠ (i : (centerQuotientCartan H).root) →
      ∀ (z : B →ₐc[K] SymmetricAlgebra K K),
        gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π k.val →
        ∀ c : K, (characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ *
            gaParameterPoint z c * characterReflectionPoint I hI π hπ hker hB (E.symm i) ∈
          borelPointsSubgroup J := by
  intro _ _ _ _ _ H E b i k hk z hz c
  have hE : ∀ x, ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm
    x) = x :=
    fun x => E.apply_symm_apply x
  have hp := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB (E.symm i)
  obtain ⟨z', -, hz', hconj⟩ := hp.rootReflectionPoint_ga_conjugation I hI π hπ hker hB
    (E.symm i) (borelRootCharacterOccurring J π k) z hz
  have hkpos := borelRootBase_isPos I J hJI hI hJ π hπ hker hB k
  have hrpos := hkpos.reflectionPerm i.property hk
  have hEi : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm i) =
    i := hE i
  rw [← hEi] at hrpos
  have hmem := SchubertCellRankOne.gaParameterPoint_mem_borel_of_isPos I J hJI hI hJ π hπ hker hB _
    z'
    hz' hrpos c
  obtain ⟨t, ht, hinv⟩ := hp.rootReflectionPoint_inv_mem_torus_mul I hπ hker
  have htB : t ∈ borelPointsSubgroup J := torusPoints_le_borelPoints I J hJI ht
  have hconj' : characterReflectionPoint I hI π hπ hker hB (E.symm i) * gaParameterPoint z c *
      (characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ = gaParameterPoint z' c :=
    hconj c
  have heq : (characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ * gaParameterPoint z c *
      characterReflectionPoint I hI π hπ hker hB (E.symm i) =
      t * gaParameterPoint z' c * t⁻¹ := by
    rw [← hconj']
    calc (characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ * gaParameterPoint z c *
          characterReflectionPoint I hI π hπ hker hB (E.symm i) =
        (characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ * gaParameterPoint z c *
          ((characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹)⁻¹ := by rw [inv_inv]
      _ = (t * characterReflectionPoint I hI π hπ hker hB (E.symm i)) * gaParameterPoint z c *
          (t * characterReflectionPoint I hI π hπ hker hB (E.symm i))⁻¹ := by
        change (rootReflectionPoint _ _)⁻¹ * _ * ((rootReflectionPoint _ _)⁻¹)⁻¹ = _
        rw [hinv]
        rfl
      _ = _ := by group
  rw [heq]
  exact mul_mem (mul_mem htB hmem) (inv_mem htB)

-- The Borel factorization separates the simple-root subgroup from the complementary
-- positive-root product and transports its coordinates through torus conjugation.
set_option maxHeartbeats 1000000 in
/-- **`B(K) n_i ⊆ x_i(K) n_i B(K)`** for every simple root `i` of the Borel
base. -/
theorem reductive_borel_mul_reflectionPoint
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let b := borelRootBase I J hJI hI hJ π hπ hker hB
    ∀ (i : b.support) (g : WithConv (B →ₐ[K] K)), g ∈ borelPointsSubgroup J →
      ∃ c : K, ∃ g' ∈ borelPointsSubgroup J,
        g * characterReflectionPoint I hI π hπ hker hB (E.symm i) =
          gaParameterPoint (characterSl2PairChoice I hI π hπ hker hB (E.symm i)).1 c *
            characterReflectionPoint I hI π hπ hker hB (E.symm i) * g' := by
  intro _ _ _ _ _ E b i g hg
  classical
  have hE : ∀ x, ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm
    x) = x :=
    fun x => E.apply_symm_apply x
  have hp := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB (E.symm i)
  set n := characterReflectionPoint I hI π hπ hker hB (E.symm i) with hn
  obtain ⟨t, ht, u, hu, rfl⟩ :=
    BorelPoint.exists_torus_mul_borelRootUnipotent I J hJI hI hJ π hπ hker hB g hg
  obtain ⟨xc, e, he, hxc, -⟩ := exists_borelRootCoordinateBasis I J hJI hI hJ π hπ hker hB
  have hxcU := fun k => he k ▸ (e k).property
  obtain ⟨kα, hkα⟩ := SchubertCellRankOne.exists_borelRootCharacter_of_isPos I J hJI hI hJ π hπ hker
    hB
    (i : (centerQuotientCartan (diagonalizableTangentImage π)).root)
    (b.isPos_of_mem_support i.property)
  let R₁ : Set (centerQuotientCartan (diagonalizableTangentImage π)).root :=
    leftRootInversionIndices b (RootPairing.weylGroup.ofIdx _
      (i : (centerQuotientCartan (diagonalizableTangentImage π)).root))
  let R₂ : Set (centerQuotientCartan (diagonalizableTangentImage π)).root :=
    {r | b.IsPos r ∧ r ∉ R₁}
  have hS₁ := IsBorelRootCharacterClosed.of_isPositiveRootClosed I J hJI hI hJ π hπ hker hB R₁
    (LeftRootInversionIndices.isPositiveRootClosed b _)
  have hS₂ := IsBorelRootCharacterClosed.of_isPositiveRootClosed I J hJI hI hJ π hπ hker hB R₂
    (PositiveRootClosedSets.isPositiveRootClosed b _)
  have hR₁ : R₁ = {(i : (centerQuotientCartan (diagonalizableTangentImage π)).root)} :=
    leftRootInversionIndices_simple b i
  have hunion : (Set.univ : Set (borelRootCharacterIndex J π)) =
      {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) ∈ R₁} ∪
      {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) ∈ R₂} := by
    ext k
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    by_cases hk : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) ∈ R₁
    · exact Or.inl hk
    · exact Or.inr ⟨borelRootBase_isPos I J hJI hI hJ π hπ hker hB k, hk⟩
  have hdisj : Disjoint
      {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) ∈ R₁}
      {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) ∈ R₂} :=
    Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1
  have hsu : IsBorelRootCharacterClosed J π Set.univ := fun _ _ _ _ => Set.mem_univ _
  have huU : (⟨u, hu⟩ : borelRootUnipotentPoints J π hπ) ∈
      borelRootSubsetPoints J hJ π hπ e Set.univ := fun k hk => absurd (Set.mem_univ k) hk
  obtain ⟨⟨u₁, u₂⟩, ⟨hu₁, hu₂, hprod⟩, -⟩ := borelRootSubsetPoints_existsUnique_mul I J hJI hI hJ
    π hπ hker hB xc e he hxc hsu hS₁ hS₂ hunion hdisj _ huU
  have hkαS : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
      (borelRootCharacterOccurring J π kα) ∈ R₁ := by
    rw [hkα, hE, hR₁]
    rfl
  have hsingle : ∀ k ∈ {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker
    hB
      (borelRootCharacterOccurring J π k) ∈ R₁}, k = kα := by
    intro k hk
    have h1 : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π k) = i := by
      have hk' : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
          (borelRootCharacterOccurring J π k) ∈ R₁ := hk
      rw [hR₁] at hk'
      exact hk'
    have h2 : borelRootCharacterOccurring J π k = borelRootCharacterOccurring J π kα := by
      apply (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB).injective
      rw [h1, hkα, hE]
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hkαval : kα.val =
      (E.symm (i : (centerQuotientCartan (diagonalizableTangentImage π)).root)).val :=
    congrArg Subtype.val hkα
  have hpα : IsRootSl2Pair π kα.val (characterSl2PairChoice I hI π hπ hker hB (E.symm i)).1
      (characterSl2PairChoice I hI π hπ hker hB (E.symm i)).2 := by
    rw [hkαval]
    exact hp
  obtain ⟨c₁, hc₁⟩ := BorelRootSubsetPoints.singleton_eq_gaParameterPoint I J hJI hI hJ π hπ hker
    hB xc e he hxc hS₁ kα hkαS hsingle hpα u₁ hu₁
  obtain ⟨c₂, hc₂⟩ := torusPoint_conj_gaParameterPoint I π hπ hker hp.tangent_mem ht c₁
  let _ : Finite (borelRootCharacterIndex J π) := finite_borelRootCharacterIndex J π hπ
  let S₂ := {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    (borelRootCharacterOccurring J π k) ∈ R₂}
  let _ : Fintype S₂ := Fintype.ofFinite _
  let l₂ : List S₂ := (Finset.univ : Finset S₂).toList
  obtain ⟨a₂, ha₂⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB xc e he hxc
    hxcU hS₂ l₂ (Finset.nodup_toList _) (fun j => Finset.mem_toList.mpr (Finset.mem_univ j))
    u₂ hu₂
  have hconjB := SchubertCellRankOne.reflectionPoint_conj_ga_mem_borel I J hJI hI hJ π hπ hker hB i
  have hu₂conj : n⁻¹ * (u₂ : WithConv (B →ₐ[K] K)) * n ∈ borelPointsSubgroup J := by
    rw [← ha₂]
    change n⁻¹ * (l₂.map fun j : S₂ => gaParameterPoint (xc j.val) (a₂ j)).prod * n ∈ _
    have hlist : n⁻¹ * (l₂.map fun j : S₂ => gaParameterPoint (xc j.val) (a₂ j)).prod * n =
        (l₂.map fun j : S₂ => n⁻¹ * gaParameterPoint (xc j.val) (a₂ j) * n).prod := by
      have h := map_list_prod (MulAut.conj n⁻¹).toMonoidHom
        (l₂.map fun j : S₂ => gaParameterPoint (xc j.val) (a₂ j))
      simp only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv] at h
      exact h
    rw [hlist]
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
    have hj : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π j.val) ≠ i := by
      intro heq
      apply j.property.2
      show _ ∈ R₁
      rw [heq, hR₁]
      rfl
    exact hconjB j.val hj (xc j.val) (hxc j.val) (a₂ j)
  have htn : n⁻¹ * t * n ∈ borelPointsSubgroup J := by
    have hN := inv_mem (hp.rootReflectionPoint_mem_normalizer I hπ hker)
    have := (Subgroup.mem_normalizer_iff.mp hN t).mp ht
    rw [inv_inv] at this
    exact torusPoints_le_borelPoints I J hJI this
  refine ⟨c₂, n⁻¹ * t * n * (n⁻¹ * u₂ * n), mul_mem htn hu₂conj, ?_⟩
  have hu_eq : u = (u₁ : WithConv (B →ₐ[K] K)) * u₂ := congrArg Subtype.val hprod.symm
  rw [← hc₂, hu_eq, hc₁]
  group

/-- **The Bruhat system of the reductive group.** For the Borel base,
the Borel points `B(K)`, the torus points `T(K)`, the chosen reflection points
`n_r` and the chosen root subgroups `x_i, y_i` of the simple roots satisfy all
hypotheses of `IsBruhatSystem`. -/
theorem reductive_isBruhatSystem
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let b := borelRootBase I J hJI hI hJ π hπ hker hB
    IsBruhatSystem b (borelPointsSubgroup J)
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K))
      (fun r => characterReflectionPoint I hI π hπ hker hB (E.symm r))
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv :
            Derivation K B (Bialgebra.CounitAlgebra K B K) →ₗ[K]
              Derivation K B (Bialgebra.CounitAlgebra K B K)) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val)
      (fun i c => gaParameterPoint (characterSl2PairChoice I hI π hπ hker hB (E.symm i)).1 c)
      (fun i c => gaParameterPoint (characterSl2PairChoice I hI π hπ hker hB (E.symm i)).2 c) := by
  intro _ _ _ _ _ E b
  have hsys := reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  have hBpos := SchubertCellRankOne.gaParameterPoint_mem_borel_of_isPos I J hJI hI hJ π hπ hker hB
  have hmul := reductive_borel_mul_reflectionPoint I J hJI hI hJ π hπ hker hB
  refine ⟨torusPoints_le_borelPoints I J hJI, hsys, ?_, ?_⟩
  · intro i
    have hp := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB (E.symm i)
    refine ⟨torusPoints_le_borelPoints I J hJI, ?_, gaParameterPoint_zero _,
      gaParameterPoint_zero _, ?_, hp.rootReflectionPoint_mem_normalizer I hπ hker,
      hp.rootReflectionPoint_inv_mem_torus_mul I hπ hker, hmul i, ?_⟩
    · intro c
      exact hBpos i _ hp.tangent_mem (b.isPos_of_mem_support i.property) c
    · intro d hd
      exact hp.partner_point_eq_mul_torus_mul I hπ hker hd
    · intro c
      exact IsRootSl2Pair.conj_partner I hI π hπ hker hB hp c
  · intro w i hpos c
    have hp := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB (E.symm i)
    obtain ⟨z', -, hz', hconj⟩ := ga_conjugation_of_characterSpace_map π hπ _ _ _
      (E.symm _).property.2 (hsys.weylElementPoint_transport b w i) _ hp.tangent_mem
    have hmem : gaAffineGroupPoints z' (Multiplicative.ofAdd c) ∈ borelPointsSubgroup J :=
      hBpos _ z' hz' hpos c
    rw [← hconj c] at hmem
    exact hmem

end ReductiveGroups
