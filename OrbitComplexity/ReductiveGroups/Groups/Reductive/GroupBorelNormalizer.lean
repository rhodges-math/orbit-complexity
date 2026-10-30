import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootDecomposition
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusCentralizerTangent
import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialBijection
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPointSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent

/-!
# The torus normalizer inside a Borel subgroup

The unipotent radical has no nonidentity point centralizing the maximal torus.
Its tangent lies in both the zero torus weight and the unipotent tangent, so it
vanishes. The torus-unipotent factorization then identifies the Borel normalizer
intersection with the torus.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A unipotent Borel point centralizing the maximal torus is the identity. -/
theorem unipotent_eq_one_of_centralizes (g : G.points) (hg : g ∈ G.unipotentPoints)
    (hcomm : ∀ t ∈ G.torusPoints, t * g = g * t) : g = 1 := by
  have hfix : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra)
      (torusConjugationFixedHopfIdeal G.torusSplit) (CommAlgCat.of K K) := by
    apply (mem_torusConjugationFixed_iff G.torusSplit g).mpr
    intro z
    have ht := mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective
      G.split_eq_zero z
    simpa only [show IsScalarTower.toAlgHom K K K = AlgHom.id K K from rfl,
      AlgHom.id_comp, WithConv.toConv_ofConv] using hcomm _ ht
  have hd : Disjoint
      (hopfTangentImage (torusConjugationFixedHopfIdeal G.torusSplit)).toSubmodule
      G.unipotentTangent.toSubmodule := by
    rw [TorusConjugationFixed.tangentImage_eq_identityWeight,
      G.identityWeightSpace_eq_torus]
    exact G.torus_disjoint_unipotent
  obtain ⟨φ, hφ, _⟩ := BorelRootExponentialBijection.existsUnique_of_borelRootUnipotentPoint
    G.borelIdeal G.isBorel G.torusSplit G.split_surjective g hg
  rw [← hφ]
  exact gaPoint_one_eq_one_of_disjoint φ
    (torusConjugationFixedHopfIdeal G.torusSplit) G.unipotentIdeal hd
    (by rwa [hφ]) (by rwa [hφ])

/-- The Borel points normalizing the maximal torus are exactly the torus points. -/
theorem borel_inf_torus_normalizer :
    G.borelPoints ⊓ Subgroup.normalizer (G.torusPoints : Set G.points) = G.torusPoints := by
  apply le_antisymm
  · rintro n ⟨hnB, hnN⟩
    obtain ⟨t, ht, u, hu, htu⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
      G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
      G.split_surjective G.split_eq_zero G.reductive n hnB
    have huN : u ∈ Subgroup.normalizer (G.torusPoints : Set G.points) := by
      have h := (Subgroup.normalizer (G.torusPoints : Set G.points)).mul_mem
        ((Subgroup.normalizer _).inv_mem (G.torusPoints.le_normalizer ht)) hnN
      rwa [← htu, inv_mul_cancel_left] at h
    have hcomm : ∀ s ∈ G.torusPoints, s * u = u * s := by
      intro s hs
      have hcT : u * s * u⁻¹ * s⁻¹ ∈ G.torusPoints := G.torusPoints.mul_mem
        ((Subgroup.mem_normalizer_iff.mp huN s).mp hs) (G.torusPoints.inv_mem hs)
      have hsN := TorusPoints.le_normalizer_borelRootUnipotentPoints G.torusIdeal
        G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
        G.split_surjective G.split_eq_zero G.reductive hs
      have hsU : s * u⁻¹ * s⁻¹ ∈ G.unipotentPoints :=
        (Subgroup.mem_normalizer_iff.mp hsN u⁻¹).mp (G.unipotentPoints.inv_mem hu)
      have hcU : u * s * u⁻¹ * s⁻¹ ∈ G.unipotentPoints := by
        simpa only [mul_assoc] using G.unipotentPoints.mul_mem hu hsU
      have hc := BorelRootUnipotent.torus_point_intersection_eq_one G.torusIdeal
        G.borelIdeal G.isBorel G.torusSplit G.split_surjective G.split_eq_zero
        (u * s * u⁻¹ * s⁻¹) hcT hcU
      have hc' : u * s * u⁻¹ = s := mul_inv_eq_one.mp hc
      exact ((mul_inv_eq_iff_eq_mul).mp hc').symm
    have hu1 := G.unipotent_eq_one_of_centralizes u hu hcomm
    rw [← htu, hu1, mul_one]
    exact ht
  · intro t ht
    exact ⟨G.torus_le_borel ht, G.torusPoints.le_normalizer ht⟩

end ReductiveGroups.ReductiveGroupData
