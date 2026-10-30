import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus

/-!
# Torus points fixing a positive-root subgroup

Root characters evaluate conjugation on ordered root coordinates. If all
supported characters have value one, every subgroup point is fixed.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A torus point trivial on every supported root character fixes the root subgroup pointwise. -/
theorem rootSubsetPoints_fixed (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (hchar : ∀ i : G.rootCharacters R, z.ofConv (MonoidAlgebra.single i.val.val 1) = 1)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    AlgHom.mapDomain G.torusSplit z * g * (AlgHom.mapDomain G.torusSplit z)⁻¹ = g := by
  classical
  have hmap := (congrArg (fun H : Subgroup G.points => g ∈ H)
    (G.rootSubsetPoints_eq R hR)).mp hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hmap
  let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let _ : Fintype (G.rootCharacters R) := Fintype.ofFinite _
  let l : List (G.rootCharacters R) := Finset.univ.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hall : ∀ i, i ∈ l := by intro i; exact Finset.mem_toList.mpr (Finset.mem_univ i)
  have hxU (i) : gaAffineGroupTangent (G.borelRootMaps i) ∈ G.unipotentTangent :=
    G.borelRootBasis_tangent i ▸ (G.borelRootBasis i).property
  obtain ⟨a, ha⟩ := borelRootSubsetProduct_surjective G.torusIdeal G.borelIdeal
    G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent
    G.borelRootMaps_weight hxU (G.rootCharacters_closed R hR) l hl hall u hu
  have hc := borelRootSubsetProduct_torus_conj G.borelIdeal G.torusSplit G.split_surjective
    G.borelRootMaps hxU G.borelRootMaps_weight (G.rootCharacters R) l a z
  have hc' : AlgHom.mapDomain G.torusSplit z *
      (borelRootSubsetProduct G.borelIdeal G.torusSplit G.split_surjective
        G.borelRootMaps hxU (G.rootCharacters R) l a).val *
      (AlgHom.mapDomain G.torusSplit z)⁻¹ =
      (borelRootSubsetProduct G.borelIdeal G.torusSplit G.split_surjective
        G.borelRootMaps hxU (G.rootCharacters R) l a).val := by
    simpa only [hchar, one_mul] using hc
  exact ((congrArg (fun q : G.unipotentPoints =>
      AlgHom.mapDomain G.torusSplit z * q.val *
        (AlgHom.mapDomain G.torusSplit z)⁻¹) ha).symm.trans hc').trans
    (congrArg Subtype.val ha)

end ReductiveGroups.ReductiveGroupData
