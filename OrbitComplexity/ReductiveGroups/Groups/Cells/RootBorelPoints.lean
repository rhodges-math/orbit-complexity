import OrbitComplexity.ReductiveGroups.Groups.Cells.SchubertCellAbstract
import OrbitComplexity.ReductiveGroups.Groups.Cells.SchubertCellDefs
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubsetGroup
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSubsetTorus
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateBasis
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneSweepClosed

/-! # Positive root subgroup points in a Borel subgroup -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

/-- The reflection point of an `sl₂`-normalized pair conjugates the root
subgroup `x` into the partner root subgroup `y`. -/
theorem IsRootSl2Pair.conj_partner
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    {α : Multiplicative (ι →₀ ℤ)} {x y : B →ₐc[K] SymmetricAlgebra K K}
    (hp : IsRootSl2Pair π α x y) (c : K) :
    ∃ c' : K, rootReflectionPoint x y * gaAffineGroupPoints x (Multiplicative.ofAdd c) *
        (rootReflectionPoint x y)⁻¹ = gaAffineGroupPoints y (Multiplicative.ofAdd c') := by
  let H := diagonalizableTangentImage π
  have hAd := hp.adjoint_rootReflectionPoint_mem hπ
  have honto := hp.adjoint_rootReflectionPoint_onto hπ
  have hh2 := hp.characterDifferential_bracket hπ
  have hroot : affineGroupAdjointRepresentation (rootReflectionPoint x y)
      (gaAffineGroupTangent x) ∈
        rootSpace H (characterDifferentialOnImage π hπ α⁻¹) := by
    apply AffineGroupAdjoint.mem_rootSpace_of_eigen_transport H (rootReflectionPoint x y)
      (characterDifferentialOnImage π hπ α) (characterDifferentialOnImage π hπ α⁻¹) hAd honto
    · intro t
      have hR : (⟨_, hAd t⟩ : H) = t - characterDifferentialOnImage π hπ α t •
          (⟨_, hp.bracket_mem⟩ : H) :=
        Subtype.ext (hp.adjoint_rootReflectionPoint hπ t)
      rw [hR, characterDifferentialOnImage_inv, LinearMap.neg_apply, map_sub, map_smul, hh2,
        smul_eq_mul]
      ring
    · exact RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α _ hp.tangent_mem
  have hmem : affineGroupAdjointRepresentation (rootReflectionPoint x y)
      (gaAffineGroupTangent x) ∈ affineGroupCharacterWeightSpace π α⁻¹ := by
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α⁻¹]
    exact hroot
  have hfin := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB α⁻¹
    (inv_ne_one.mpr (hp.ne_one hπ)) hp.partner_characterWeightSpace_ne_bot
  have h0 : (⟨gaAffineGroupTangent y, hp.partner_tangent_mem⟩ :
      affineGroupCharacterWeightSpace π α⁻¹) ≠ 0 := by
    intro hz
    exact hp.partner_tangent_ne_zero (congrArg Subtype.val hz)
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).mp hfin ⟨_, hmem⟩
  have hμx : affineGroupAdjointRepresentation (rootReflectionPoint x y)
      (gaAffineGroupTangent x) = μ • gaAffineGroupTangent y := (congrArg Subtype.val hμ).symm
  exact ⟨μ * c, GaAffineGroupPoints.conjugate_of_tangent_eq x y _ μ hμx c⟩

omit [IsAlgClosed K] [Finite ι] in
/-- Torus points conjugate a root subgroup into itself. -/
theorem torusPoint_conj_gaParameterPoint (I : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    {α : Multiplicative (ι →₀ ℤ)} {x : B →ₐc[K] SymmetricAlgebra K K}
    (hx : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α)
    {t : WithConv (B →ₐ[K] K)}
    (ht : t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K))
    (c : K) : ∃ c' : K, t * gaParameterPoint x c * t⁻¹ = gaParameterPoint x c' := by
  obtain ⟨τ, rfl⟩ := (mem_torusPoints_iff I π hπ hker t).mp ht
  exact ⟨_, GaAffineGroupPoints.conjugate_of_character_weight π α τ x hx c⟩

/-- A point of `U_S` for a closed set `S = {k_α}` is a point of the root
subgroup `x` of any `sl₂`-normalized pair for the character of `k_α`. -/
theorem BorelRootSubsetPoints.singleton_eq_gaParameterPoint
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (xc : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K)
    (e : Module.Basis (borelRootCharacterIndex J π) K
      (derivationCompLieHom (B := K) (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (he : ∀ i, (e i).val = gaAffineGroupTangent (xc i))
    (hxc : ∀ i, gaAffineGroupTangent (xc i) ∈ affineGroupCharacterWeightSpace π i.val)
    {S : Set (borelRootCharacterIndex J π)} (hS : IsBorelRootCharacterClosed J π S)
    (kα : borelRootCharacterIndex J π) (hkα : kα ∈ S) (hsingle : ∀ k ∈ S, k = kα)
    {x y : B →ₐc[K] SymmetricAlgebra K K} (hp : IsRootSl2Pair π kα.val x y)
    (u₁ : borelRootUnipotentPoints J π hπ)
    (hu₁ : u₁ ∈ borelRootSubsetPoints J hJ π hπ e S) :
    ∃ c : K, (u₁ : WithConv (B →ₐ[K] K)) = gaParameterPoint x c := by
  have hxcU := fun k => he k ▸ (e k).property
  obtain ⟨a, ha⟩ := borelRootSubsetProduct_surjective I J hJI hI hJ π hπ hker hB xc e he hxc
    hxcU hS [⟨kα, hkα⟩] (List.nodup_singleton _)
    (fun j => by
      rw [List.mem_singleton]
      exact Subtype.ext (hsingle j.val j.property)) u₁ hu₁
  have hu : (u₁ : WithConv (B →ₐ[K] K)) = gaParameterPoint (xc kα) (a ⟨kα, hkα⟩) := by
    rw [← ha]
    simp only [borelRootSubsetProduct, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  have hfin := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB kα.val
    (hp.ne_one hπ) hp.characterWeightSpace_ne_bot
  have h0 : (⟨gaAffineGroupTangent x, hp.tangent_mem⟩ :
      affineGroupCharacterWeightSpace π kα.val) ≠ 0 := by
    intro hz
    exact hp.tangent_ne_zero (congrArg Subtype.val hz)
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).mp hfin ⟨_, hxc kα⟩
  have hμx : affineGroupAdjointRepresentation (1 : WithConv (B →ₐ[K] K))
      (gaAffineGroupTangent (xc kα)) = μ • gaAffineGroupTangent x := by
    rw [map_one, Module.End.one_apply]
    exact (congrArg Subtype.val hμ).symm
  have hconj := GaAffineGroupPoints.conjugate_of_tangent_eq (xc kα) x 1 μ hμx (a ⟨kα, hkα⟩)
  rw [one_mul, inv_one, mul_one] at hconj
  exact ⟨μ * a ⟨kα, hkα⟩, hu.trans hconj⟩

/-- A root subgroup whose root is positive for the Borel base consists
of Borel points. -/
theorem SchubertCellRankOne.gaParameterPoint_mem_borel_of_isPos
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
    ∀ (r : (centerQuotientCartan H).root) (z : B →ₐc[K] SymmetricAlgebra K K),
      gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π (E.symm r).val →
      (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos r →
      ∀ c : K, gaParameterPoint z c ∈ borelPointsSubgroup J := by
  intro _ _ _ _ _ H E r z hz hpos c
  have hE : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm r) =
    r :=
    E.apply_symm_apply r
  have hpos' : (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos
      (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm r)) := by
    rw [hE]
    exact hpos
  have hJmem := (borelRootBase_isPos_iff I J hJI hI hJ π hπ hker hB (E.symm r)).mp hpos' _ hz
  exact GaParameterPoint.mem_of_tangent_mem_quotient z J hJmem c

/-- A positive root of the Borel base is the root of a Borel root character. -/
theorem SchubertCellRankOne.exists_borelRootCharacter_of_isPos
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
    ∀ r : (centerQuotientCartan H).root,
      (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos r →
      ∃ k : borelRootCharacterIndex J π, borelRootCharacterOccurring J π k = E.symm r := by
  intro _ _ _ _ _ H E r hpos
  have hE : ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm r) =
    r :=
    E.apply_symm_apply r
  have hpos' : (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos
      (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm r)) := by
    rw [hE]
    exact hpos
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (E.symm r).property.1
  have hJmem := (borelRootBase_isPos_iff I J hJI hI hJ π hπ hker hB (E.symm r)).mp hpos' d hd
  refine ⟨⟨(E.symm r).val, (E.symm r).property.2, ?_⟩, Subtype.ext rfl⟩
  intro hbot
  have hmem : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
        affineGroupCharacterWeightSpace π (E.symm r).val := ⟨hJmem, hd⟩
  rw [hbot] at hmem
  exact hd0 ((Submodule.mem_bot K).mp hmem)

end ReductiveGroups
