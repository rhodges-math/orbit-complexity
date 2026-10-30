import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSupport
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootDecomposition
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootObstruction
import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableCartanRootDecomposition

/-!
# Solvable maximality of Levi Borel tangents

The Cartan weight decomposition of a solvable tangent enlargement has no
root weights outside the selected simple-root span. Within that span,
opposite root spaces obstruct solvability, so only the positive Levi roots
can occur.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti LieAlgebra
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem torusTangent_le_leviBorel (I : Set G.rootBase.support) :
    G.torusTangent ≤ G.subgroupTangent (G.leviBorelIdeal I) := by
  rintro d ⟨t, rfl⟩
  apply (tangent_mem_hopfQuotient_iff (G.leviBorelIdeal I) _).mpr
  intro a ha
  change t (G.torusSplit a) = 0
  rw [(G.split_eq_zero a).mpr (G.leviBorelIdeal_le_torus I ha), map_zero]

private theorem rootReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toIdeal) := by
  change IsReduced (G.rootSubsetAlgebra _ _)
  infer_instance
attribute [local instance] rootReduced

private theorem leviBorelIdeal_le_root (I : Set G.rootBase.support) :
    G.leviBorelIdeal I ≤ G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  exact (G.rootSubsetPoints_le_leviBorel I _ _ (fun _ h => h)).trans_eq
    (G.leviBorelIdeal_points I).symm

private theorem rootWeightSpace_le_leviBorel (I : Set G.rootBase.support) (r : G.rootIndex)
    (hr : r ∈ leviPositiveRoots G.rootBase I) :
    G.rootWeightSpace r ≤ (G.subgroupTangent (G.leviBorelIdeal I)).toSubmodule :=
  (G.rootWeightSpace_le_rootSubset _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)
    r hr.1 hr).trans
      (hopfQuotient_tangentImage_antitone _ _ (leviBorelIdeal_le_root G I))

private theorem rootCharacter_neg (r : G.rootIndex) :
    G.rootCharacter (-r) = (G.rootCharacter r)⁻¹ := by
  have h : G.rootSystem.rootSpanMem ℤ (-r) = -G.rootSystem.rootSpanMem ℤ r := by
    apply Subtype.ext
    simp
  have hm := congrArg G.rootCharacterMap h
  rw [map_neg, G.rootCharacterMap_root, G.rootCharacterMap_root] at hm
  exact hm

private theorem pos_mem_levi_of_span (I : Set G.rootBase.support) (r : G.rootIndex)
    (hr : G.rootBase.IsPos r)
    (hs : G.rootSystem.root r ∈ Submodule.span K (G.rootBase.toWeightBasis '' I)) :
    r ∈ leviPositiveRoots G.rootBase I := by
  by_contra hn
  have hnot := LeviRootSpan.notMem_span_of_notMem_leviPositiveRoots G.rootBase I hr hn
  have he : Set.range (fun j : I => G.rootSystem.root j.val.val) =
      G.rootBase.toWeightBasis '' I := by
    ext v
    simp [RootPairing.Base.toWeightBasis_apply]
  exact hnot (he.symm ▸ hs)

private theorem leviSolvable_weight_mem (I : Set G.rootBase.support)
    (S : LieSubalgebra K G.tangent) [LieAlgebra.IsSolvable S]
    (hBS : G.subgroupTangent (G.leviBorelIdeal I) ≤ S)
    (hSL : S ≤ G.subgroupTangent (G.leviIdeal I))
    (r : G.rootIndex) (d : G.tangent) (hdS : d ∈ S) (hdW : d ∈ G.rootWeightSpace r) :
    d ∈ G.subgroupTangent (G.leviBorelIdeal I) := by
  by_cases hd0 : d = 0
  · exact hd0 ▸ (G.subgroupTangent (G.leviBorelIdeal I)).zero_mem
  have hs : G.rootSystem.root r ∈ Submodule.span K (G.rootBase.toWeightBasis '' I) := by
    by_contra hn
    exact hd0 (G.leviTangent_eq_zero_of_root I r hn d (hSL hdS) hdW)
  by_cases hr : G.rootBase.IsPos r
  · exact rootWeightSpace_le_leviBorel G I r (pos_mem_levi_of_span G I r hr hs) hdW
  · have hnpos : G.rootBase.IsPos (-r) := by
      have h := (isPos_neg_index_iff G.rootBase r).mpr hr
      simpa only [LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg] using h
    have hnspan : G.rootSystem.root (-r) ∈
        Submodule.span K (G.rootBase.toWeightBasis '' I) := by
      change -G.rootSystem.root r ∈ Submodule.span K (G.rootBase.toWeightBasis '' I)
      exact Submodule.neg_mem _ hs
    have hneg := (rootWeightSpace_le_leviBorel G I (-r)
      (pos_mem_levi_of_span G I (-r) hnpos hnspan)).trans hBS
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one (G.rootWeightSpace_finrank r)
      hdW hd0
    have hpos : G.rootWeightSpace r ≤ S.toSubmodule := by
      rw [hspan]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hdS)
    exact False.elim (SolvableTangent.not_contains_opposite_characterWeights
      G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero
      G.reductive S (G.rootCharacter r) (G.rootCharacter_ne_one r)
      (G.rootWeightSpace_ne_bot r) (fun x hx => hpos hx) (by
        intro x hx
        apply hneg
        change x ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter (-r))
        rwa [rootCharacter_neg]))

/-- The Levi Borel tangent is maximal among solvable subalgebras of the Levi tangent. -/
theorem leviBorelTangent_maximal (I : Set G.rootBase.support)
    (S : LieSubalgebra K G.tangent) [LieAlgebra.IsSolvable S]
    (hBS : G.subgroupTangent (G.leviBorelIdeal I) ≤ S)
    (hSL : S ≤ G.subgroupTangent (G.leviIdeal I)) :
    S = G.subgroupTangent (G.leviBorelIdeal I) := by
  let H := G.torusTangent
  let D := G.subgroupTangent (G.leviBorelIdeal I)
  have hHD : H ≤ D := torusTangent_le_leviBorel G I
  have hHS : H ≤ S := hHD.trans hBS
  have hSD : cartanStableSubmodule H S hHS ≤ cartanStableSubmodule H D hHD := by
    rw [CartanStableSubmodule.eq_iSup_inf_rootSpace H S hHS]
    refine iSup_le fun χ => ?_
    intro d hd
    have hdS : (d : G.tangent) ∈ S := hd.1
    have hdroot : (d : G.tangent) ∈ LieAlgebra.rootSpace H χ := hd.2
    by_cases hχ : χ.IsZero
    · have hz : LieAlgebra.rootSpace H χ = H.toLieSubmodule := by
        simpa only [hχ.eq] using (LieAlgebra.rootSpace_zero_eq K G.tangent H)
      rw [hz] at hdroot
      exact hHD hdroot
    · obtain ⟨α, ⟨_, hαχ⟩, _⟩ := existsUnique_character_of_lieWeight G.torusSplit
        G.split_surjective χ
      have hα : α ≠ 1 := by
        intro hα1
        apply hχ
        change (χ : H → K) = 0
        rw [hαχ, hα1, characterDifferentialOnImage_one]
        rfl
      have hdW : (d : G.tangent) ∈ affineGroupCharacterWeightSpace G.torusSplit α := by
        rw [AffineGroupCharacterWeightSpace.eq_rootSpace G.torusSplit G.split_surjective α]
        change (d : G.tangent) ∈ LieAlgebra.rootSpace H
          (characterDifferentialOnImage G.torusSplit G.split_surjective α)
        exact hαχ ▸ hdroot
      by_cases hd0 : (d : G.tangent) = 0
      · exact hd0 ▸ D.zero_mem
      have hW : affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ := by
        intro he
        exact hd0 (by simpa only [he, Submodule.mem_bot] using hdW)
      let a := (⟨α, hW, hα⟩ : {α : G.characters //
        affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ ∧ α ≠ 1})
      let r := G.characterRootEquiv a
      have he : G.rootCharacter r = α := by
        change (G.characterRootEquiv.symm (G.characterRootEquiv a)).val = α
        rw [Equiv.symm_apply_apply]
      apply leviSolvable_weight_mem G I S hBS hSL r d hdS
      change (d : G.tangent) ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
      rwa [he]
  apply le_antisymm _ hBS
  intro d hd
  exact hSD hd

end ReductiveGroups.ReductiveGroupData
