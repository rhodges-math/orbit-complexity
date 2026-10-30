import OrbitComplexity.Paper.Heart.TrivialComplement
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Longest
import OrbitComplexity.SchubertGeometry.Roots.Products
import OrbitComplexity.GroupActions.Varieties.RootProductPoints
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complementary positive roots in a Levi Borel -/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry TauCeti
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem complement_eq (I : Set G.rootBase.support) (w : G.weylGroup) :
    complementRootIndices G I w = leviPositiveRoots G.rootBase I \
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) := by
  ext r
  simp only [complementRootIndices, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
  exact and_congr_right fun hr => and_iff_right hr.1

private theorem levi_root_partition (I : Set G.rootBase.support) (w : G.weylGroup) :
    leviPositiveRoots G.rootBase I = complementRootIndices G I w ∪
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) := by
  rw [complement_eq]
  exact (Set.sdiff_union_of_subset (parabolic_inversions_subset G.rootBase I _
    (leftParabolicFactor_mem G.rootBase I w))).symm

private theorem levi_root_disjoint (I : Set G.rootBase.support) (w : G.weylGroup) :
    Disjoint (complementRootIndices G I w)
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w)) := by
  rw [complement_eq]
  exact Set.disjoint_sdiff_left

/-- The complementary root group is closed, normalized and gives the remaining Levi root factor. -/
theorem leviBorel_complement (I : Set G.rootBase.support) (w : G.weylGroup) :
    complementRootIndices G I w = leviPositiveRoots G.rootBase I \
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) ∧
    IsClosedImmersion (rootSubsetInclusion G (complementRootIndices G I w)
      (complementRootIndices_closed G I w)).left ∧
    IsMonHom (rootSubsetInclusion G (complementRootIndices G I w)
      (complementRootIndices_closed G I w)) ∧
    G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) ≤
      G.unipotentPoints ∧
    G.torusPoints ≤ Subgroup.normalizer
      (G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) : Set G.points) ∧
    (G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) = ⊥ ↔
      leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ∧
    ((G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) : Set G.points) *
      (G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) : Set G.points) =
      (G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) : Set G.points)) ∧
    (∃ e : (rootProductVariety G (complementRootIndices G I w)
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (complementRootIndices_closed G I w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toOver ≅
        (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
          (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toOver,
      e.hom ≫ rootSubsetInclusion G (leviPositiveRoots G.rootBase I)
          (LeviRootSpan.isPositiveRootClosed G.rootBase I) =
        (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (affineMulMap
          (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (complementRootIndices G I w)
            (complementRootIndices_closed G I w)).toIdeal)
          (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
            (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
            (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal))).op) ∧
    ∀ (l : List (G.rootCharacters (complementRootIndices G I w)))
      (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      ∃ e : (affineSpaceVariety K (G.rootCharacters (complementRootIndices G I w))).toOver ≅
          (complementUnipotent G I w).toOver,
        (∀ a : G.rootCharacters (complementRootIndices G I w) → K,
          (rootSubsetPointsMulEquiv G _ _ (Variety.mapPoints e.hom
            ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
              (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
        (∀ f : (i : G.rootCharacters (complementRootIndices G I w)) →
            rootSubgroupPoints G (G.characterRootEquiv
              (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
          (l.map (fun i => (f i : G.points))).prod ∈
            G.rootSubsetPoints (complementRootIndices G I w)
              (complementRootIndices_closed G I w)) ∧
        ∀ g : G.points, g ∈ G.rootSubsetPoints (complementRootIndices G I w)
            (complementRootIndices_closed G I w) →
          ∃! f : (i : G.rootCharacters (complementRootIndices G I w)) →
              rootSubgroupPoints G (G.characterRootEquiv
                (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
            (l.map (fun i => (f i : G.points))).prod = g := by
  refine ⟨complement_eq G I w, inferInstance, inferInstance,
    G.rootSubsetPoints_le_unipotent _ _,
    G.torusPoints_le_rootNormalizer _ _, ?_, ?_, ?_, ?_⟩
  · rw [← complement_eq]
    exact complement_trivial_iff G I w
  · ext g
    constructor
    · rintro ⟨u, hu, a, ha, rfl⟩
      exact (G.rootSubsetPoints _ _).mul_mem
        (G.rootSubsetPoints_mono _ _ _ _ (fun r hr => hr.1) hu)
        (G.rootSubsetPoints_mono _ _ _ _ (parabolic_inversions_subset G.rootBase I _
          (leftParabolicFactor_mem G.rootBase I w)) ha)
    · intro hg
      obtain ⟨p, ⟨hp, hq, he⟩, _⟩ := G.rootSubsetPoints_existsUnique_mul _ _ _
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) (complementRootIndices_closed G I w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
        (levi_root_partition G I w) (levi_root_disjoint G I w) g hg
      exact ⟨p.1, hp, p.2, hq, he⟩
  · exact ⟨rootProductIso G _ _ _ _ _ _ (levi_root_partition G I w)
      (levi_root_disjoint G I w), rootProductIso_hom_comp G _ _ _ _ _ _ _ _⟩
  · intro l hl hall
    exact ⟨rootSubsetProductChart G _ _ l hl hall,
      rootSubsetProductChart_points G _ _ l hl hall,
      rootSupport_directly_spanned G _ _ l hl hall⟩

/-- Complementary Levi root groups and their regular products over the complex numbers. -/
theorem leviBorel_complement_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    complementRootIndices G I w = leviPositiveRoots G.rootBase I \
      leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) ∧
    IsClosedImmersion (rootSubsetInclusion G (complementRootIndices G I w)
      (complementRootIndices_closed G I w)).left ∧
    IsMonHom (rootSubsetInclusion G (complementRootIndices G I w)
      (complementRootIndices_closed G I w)) ∧
    G.rootSubsetPoints (complementRootIndices G I w) (complementRootIndices_closed G I w) ≤
      G.unipotentPoints ∧
    G.torusPoints ≤ Subgroup.normalizer
      (G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) : Set G.points) ∧
    (G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) = ⊥ ↔
      leviPositiveRoots G.rootBase I \
        leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) = ∅) ∧
    ((G.rootSubsetPoints (complementRootIndices G I w)
        (complementRootIndices_closed G I w) : Set G.points) *
      (G.rootSubsetPoints
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) : Set G.points) =
      (G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) : Set G.points)) ∧
    (∃ e : (rootProductVariety G (complementRootIndices G I w)
        (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
        (complementRootIndices_closed G I w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toOver ≅
        (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
          (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toOver,
      e.hom ≫ rootSubsetInclusion G (leviPositiveRoots G.rootBase I)
          (LeviRootSpan.isPositiveRootClosed G.rootBase I) =
        (algSpec (CommRingCat.of ℂ)).map (CommAlgCat.ofHom (affineMulMap
          (Ideal.Quotient.mkₐ ℂ (G.rootSubsetIdeal (complementRootIndices G I w)
            (complementRootIndices_closed G I w)).toIdeal)
          (Ideal.Quotient.mkₐ ℂ (G.rootSubsetIdeal
            (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
            (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal))).op) ∧
    ∀ (l : List (G.rootCharacters (complementRootIndices G I w)))
      (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      ∃ e : (affineSpaceVariety ℂ (G.rootCharacters (complementRootIndices G I w))).toOver ≅
          (complementUnipotent G I w).toOver,
        (∀ a : G.rootCharacters (complementRootIndices G I w) → ℂ,
          (rootSubsetPointsMulEquiv G _ _ (Variety.mapPoints e.hom
            ((affineSpaceVarietyPointsEquiv ℂ _).symm a)) : G.points) =
              (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
        (∀ f : (i : G.rootCharacters (complementRootIndices G I w)) →
            rootSubgroupPoints G (G.characterRootEquiv
              (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
          (l.map (fun i => (f i : G.points))).prod ∈
            G.rootSubsetPoints (complementRootIndices G I w)
              (complementRootIndices_closed G I w)) ∧
        ∀ g : G.points, g ∈ G.rootSubsetPoints (complementRootIndices G I w)
            (complementRootIndices_closed G I w) →
          ∃! f : (i : G.rootCharacters (complementRootIndices G I w)) →
              rootSubgroupPoints G (G.characterRootEquiv
                (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
            (l.map (fun i => (f i : G.points))).prod = g :=
  leviBorel_complement G I w

end SchubertOrbits
