import OrbitComplexity.SchubertGeometry.Roots.BorelRadicals
import OrbitComplexity.SchubertGeometry.Roots.Products
import OrbitComplexity.Paper.Heart.Decomposition

/-! # Root subgroups and ordered unipotent decompositions -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti SchubertGeometry
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The root groups, Borel radicals, inversion subgroups and their ordered products. -/
theorem rootSubgroups_definition :
    G.unipotentIdeal.map (Bialgebra.Quotient.mkBialgHom G.borelIdeal.toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.borelAlgebra ∧
    G.oppositeUnipotentIdeal.map
        (Bialgebra.Quotient.mkBialgHom G.oppositeBorelIdeal.toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.oppositeBorelAlgebra ∧
    (∀ r : G.rootIndex,
      IsClosedImmersion (gaMorphism G (rootParameterMap G r)).left ∧
      gaAffineGroupTangent (rootParameterMap G r) ∈ G.rootWeightSpace r ∧
      gaAffineGroupTangent (rootParameterMap G r) ≠ 0) ∧
    (∀ r : G.rootIndex,
      (rootSubgroupPoints G r ≤ G.unipotentPoints ↔ G.rootBase.IsPos r) ∧
      (rootSubgroupPoints G r ≤ G.oppositeUnipotentPoints ↔ ¬ G.rootBase.IsPos r)) ∧
    (∀ w : G.weylGroup,
      schubertUnipotentPoints G w = G.unipotentPoints ⊓
        G.oppositeUnipotentPoints.map (MulAut.conj (G.weylPoint w)).toMonoidHom ∧
      IsClosedImmersion (rootSubsetInclusion G (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).left ∧
      G.torusPoints ≤ Subgroup.normalizer (schubertUnipotentPoints G w : Set G.points) ∧
      ∀ r : G.rootIndex, rootSubgroupPoints G r ≤ schubertUnipotentPoints G w ↔
        r ∈ leftRootInversionIndices G.rootBase w) ∧
    (∀ (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R)
      (l : List (G.rootCharacters R)) (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      ∃ e : (affineSpaceVariety K (G.rootCharacters R)).toOver ≅
          (rootSubsetVariety G R hR).toOver,
        (∀ a : G.rootCharacters R → K,
          (rootSubsetPointsMulEquiv G R hR (Variety.mapPoints e.hom
            ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
              (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
        (∀ i : G.rootCharacters R,
          Set.range (fun a : K => gaParameterPoint (G.borelRootMaps i.val) a) =
            (rootSubgroupPoints G (G.characterRootEquiv
              (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)) : Set G.points)) ∧
        (∀ u : (i : G.rootCharacters R) → rootSubgroupPoints G
            (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
          (l.map (fun i => (u i : G.points))).prod ∈ G.rootSubsetPoints R hR) ∧
        ∀ g : G.points, g ∈ G.rootSubsetPoints R hR →
          ∃! u : (i : G.rootCharacters R) → rootSubgroupPoints G
              (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
            (l.map (fun i => (u i : G.points))).prod = g) ∧
    (∀ (l : List (G.rootCharacters {r | G.rootBase.IsPos r}))
      (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      (∀ u : (i : G.rootCharacters {r | G.rootBase.IsPos r}) →
          rootSubgroupPoints G (G.rootSystem.weylGroupToPerm G.longestElement
            (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val))),
        (l.map (fun i => (u i : G.points))).prod ∈ G.oppositeUnipotentPoints) ∧
      ∀ g : G.points, g ∈ G.oppositeUnipotentPoints →
        ∃! u : (i : G.rootCharacters {r | G.rootBase.IsPos r}) →
            rootSubgroupPoints G (G.rootSystem.weylGroupToPerm G.longestElement
              (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val))),
          (l.map (fun i => (u i : G.points))).prod = g) ∧
    ∀ (w : G.weylGroup) (r : G.rootIndex),
      (rootSubgroupPoints G r).map (MulAut.conj (G.weylPoint w)).toMonoidHom =
        rootSubgroupPoints G (G.rootSystem.weylGroupToPerm w r) := by
  refine ⟨borelUnipotent_isRadical G, oppositeUnipotent_isRadical G,
    fun r => ⟨rootParameterMorphism_isClosed G r, rootParameterMap_tangent_mem G r,
      rootParameterMap_tangent_ne_zero G r⟩,
    fun r => ⟨rootSubgroup_le_unipotent G r, rootSubgroup_le_opposite G r⟩,
    ?_, ?_, opposite_directly_spanned G,
      rootSubgroup_weyl_conjugate G⟩
  · intro w
    exact ⟨G.inversionPoints_eq_inter w, inferInstance,
      G.torusPoints_le_rootNormalizer _ _, rootSubgroup_le_schubert G w⟩
  · intro R hR l hl hall
    obtain ⟨hf, hp⟩ := rootSupport_chart_factors G R hR l hl hall
    exact ⟨rootSubsetProductChart G R hR l hl hall, hp, hf,
      rootSupport_directly_spanned G R hR l hl hall⟩

/-- The conjugated parabolic factor is closed, torus-normalized and multiplies in both orders. -/
theorem rootSubgroups_parabolic (I : Set G.rootBase.support) (w : G.weylGroup) :
    (Vd.ideal G I w =
        G.rootSubsetIdeal (heartRootIndices G I w) (heartRootIndices_closed G I w) ∧
    IsClosedImmersion (Vd.inclusion G I w).left ∧
    IsMonHom (Vd.inclusion G I w) ∧
    G.torusPoints ≤ Subgroup.normalizer (Vd.points G I w : Set G.points) ∧
    Vd.points G I w ≤ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.2 ∈ Vd.points G I w ∧ p.1 * p.2 = g) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ Vd.points G I w ∧
        p.2 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.1 * p.2 = g)) ∧
    (∃ e : (GroupActions.rootProductVariety G
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (heartRootIndices G I w) (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
      (heartRootIndices_closed G I w)).toOver ≅
        (GroupActions.rootSubsetVariety G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).toOver,
      e.hom ≫
        GroupActions.rootSubsetInclusion G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (GroupActions.affineMulMap
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (heartRootIndices G I w)
          (heartRootIndices_closed G I w)).toIdeal))).op) ∧
    (∃ e : (GroupActions.rootProductVariety G (heartRootIndices G I w)
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (heartRootIndices_closed G I w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toOver ≅
        (GroupActions.rootSubsetVariety G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).toOver,
      e.hom ≫
        GroupActions.rootSubsetInclusion G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (GroupActions.affineMulMap
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (heartRootIndices G I w)
          (heartRootIndices_closed G I w)).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal))).op) :=
  ⟨directlySpannedUw G I w,
    ⟨Vd.multiplicationIso G I w, Vd.multiplicationIso_hom_comp G I w⟩,
    ⟨Vd.reverseMultiplicationIso G I w, Vd.reverseMultiplicationIso_hom_comp G I w⟩⟩

end
end SchubertOrbits
