import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSubsetTorus
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues

/-!
# Torus normalization of root-support groups

The fixed maximal torus preserves every integrally closed positive-root subgroup.
Ordered root coordinates compute conjugation by scaling each root parameter.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Torus conjugation preserves every closed positive-root subgroup on rational points. -/
theorem rootSubsetPoints_conjugate_mem (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (t g : G.points) (ht : t ∈ G.torusPoints)
    (hg : g ∈ G.rootSubsetPoints R hR) : t * g * t⁻¹ ∈ G.rootSubsetPoints R hR := by
  classical
  obtain ⟨z, rfl⟩ := (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero t).mp ht
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
  let b : G.rootCharacters R → K :=
    fun i => z.ofConv (MonoidAlgebra.single i.val.val 1) * a i
  let v := borelRootSubsetProduct G.borelIdeal G.torusSplit G.split_surjective
    G.borelRootMaps hxU (G.rootCharacters R) l b
  have hv : v ∈ borelRootSubsetSubgroup G.torusIdeal G.borelIdeal G.borel_le_torus
      G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
      G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
      (G.rootCharacters R) (G.rootCharacters_closed R hR) :=
    borelRootSubsetProduct_mem G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus
      G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive G.borelRootMaps
      G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight hxU
      (G.rootCharacters_closed R hR) l b
  have hconj : AlgHom.mapDomain G.torusSplit z * u.val *
      (AlgHom.mapDomain G.torusSplit z)⁻¹ = v.val :=
    (congrArg (fun q : G.unipotentPoints => AlgHom.mapDomain G.torusSplit z * q.val *
      (AlgHom.mapDomain G.torusSplit z)⁻¹) ha).symm.trans
        (borelRootSubsetProduct_torus_conj G.borelIdeal G.torusSplit G.split_surjective
          G.borelRootMaps hxU G.borelRootMaps_weight (G.rootCharacters R) l a z)
  apply (congrArg (fun H : Subgroup G.points =>
    AlgHom.mapDomain G.torusSplit z * u.val * (AlgHom.mapDomain G.torusSplit z)⁻¹ ∈ H)
      (G.rootSubsetPoints_eq R hR)).mpr
  exact Subgroup.mem_map.mpr ⟨v, hv, hconj.symm⟩

/-- The chosen torus normalizes every closed positive-root subgroup. -/
theorem torusPoints_le_rootNormalizer (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    G.torusPoints ≤ Subgroup.normalizer (G.rootSubsetPoints R hR : Set G.points) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact G.rootSubsetPoints_conjugate_mem R hR t g ht
  · intro hg
    have hback := G.rootSubsetPoints_conjugate_mem R hR t⁻¹ (t * g * t⁻¹)
      (G.torusPoints.inv_mem ht) hg
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hback

end ReductiveGroups.ReductiveGroupData
