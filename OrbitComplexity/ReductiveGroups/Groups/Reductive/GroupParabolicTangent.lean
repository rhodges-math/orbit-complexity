import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviComplement

/-! # Complementary tangent supports for standard parabolics

Central torus points separate the Levi tangent from the root tangents outside its subsystem.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem eq_zero_of_twice {c : K} (h : c = 2 * c) : c = 0 := by
  have h' : c + 0 = c + c := by simpa only [two_mul, add_zero] using h
  exact (add_left_cancel h').symm

private theorem root_tangent_coord_zero (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (d : G.tangent)
    (hd : d ∈ G.subgroupTangent (G.rootSubsetIdeal R hR))
    (hdU : d ∈ G.unipotentTangent)
    (i : borelRootCharacterIndex G.borelIdeal G.torusSplit)
    (hi : i ∉ G.rootCharacters R) :
    G.borelRootBasis.coord i ⟨d, hdU⟩ = 0 := by
  classical
  have hmap : (Submodule.span K (G.borelRootBasis '' G.rootCharacters R)).map
      G.unipotentTangent.toSubmodule.subtype =
      Submodule.span K ((fun j => gaAffineGroupTangent (G.borelRootMaps j)) ''
        G.rootCharacters R) := by
    rw [Submodule.map_span]
    simp only [Set.image_image, Submodule.subtype_apply,
      G.borelRootBasis_tangent]
  have hspan : d ∈ Submodule.span K
      ((fun j => gaAffineGroupTangent (G.borelRootMaps j)) '' G.rootCharacters R) := by
    rw [← G.rootSubsetTangent_eq_span R hR]
    exact hd
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp (hmap.symm ▸ hspan)
  have heq : v = (⟨d, hdU⟩ : G.unipotentTangent) := Subtype.ext he
  rw [heq] at hv
  have hs := G.borelRootBasis.mem_span_image.mp hv
  by_contra hn
  exact hi (hs (Finsupp.mem_support_iff.mpr hn))

/-- The Levi tangent and the outside-subsystem positive-root tangent have zero intersection. -/
theorem levi_disjoint_parabolicTangent (I : Set G.rootBase.support) :
    Disjoint (G.subgroupTangent (G.leviIdeal I)).toSubmodule
      (G.subgroupTangent (G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
        (parabolicRadicalRoots_closed G.rootBase I))).toSubmodule := by
  classical
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro d hd
  have hdU : d ∈ G.unipotentTangent :=
    hopfQuotient_tangentImage_antitone _ G.unipotentIdeal
      (G.unipotentIdeal_le_rootSubset _ _) hd.2
  let v : G.unipotentTangent := ⟨d, hdU⟩
  have hv : v = 0 := by
    apply G.borelRootBasis.ext_elem
    intro i
    simp only [map_zero, Finsupp.zero_apply]
    change G.borelRootBasis.coord i v = 0
    by_cases hi : i ∈ G.rootCharacters (parabolicRadicalRoots G.rootBase I)
    · have hin : i ∉ G.rootCharacters (leviPositiveRoots G.rootBase I) := by
        intro hL
        exact hi.2 hL
      obtain ⟨z, hz, hzi⟩ := exists_leviCenter_character_two G.torusIdeal G.borelIdeal
        G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
        G.split_eq_zero G.reductive I i hin
      have hf := G.leviTangent_fixed I d hd.1 (AlgHom.mapDomain G.torusSplit z)
        ⟨z, rfl, hz⟩
      have hc := borelRootCoordinateBasis_coord_torus_ad G.torusIdeal G.borelIdeal
        G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
        G.split_eq_zero G.reductive G.borelRootBasis
        (fun j => G.borelRootBasis_tangent j ▸ G.borelRootMaps_weight j) z i v
      have he : (⟨affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z) v.val,
          borelRootUnipotentTangent_torus_ad_mem G.torusIdeal G.borelIdeal
            G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
            G.split_eq_zero G.reductive z v⟩ : G.unipotentTangent) = v :=
        Subtype.ext hf
      have hc' := (congrArg (G.borelRootBasis.coord i) he).symm.trans hc
      rw [hzi] at hc'
      exact eq_zero_of_twice hc'
    · exact root_tangent_coord_zero G _ _ d hd.2 hdU i hi
  have hzero : d = 0 := congrArg Subtype.val hv
  exact hzero

end ReductiveGroups.ReductiveGroupData
