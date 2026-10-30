import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIntersection
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Longest
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviWeyl

/-!
# Opposite Levi Borel intersections

The parabolic longest element conjugates the positive Levi-root subgroup
into the opposite unipotent subgroup. Factoring a Levi Borel point into its
torus and unipotent factors identifies the intersection of the two Levi
Borels with the torus.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A Levi Borel point lying in its parabolic-longest conjugate lies in the torus. -/
theorem leviBorel_mem_torus_of_conj (I : Set G.rootBase.support) (b : G.points)
    (hb : b ∈ G.leviBorelPoints I)
    (hc : (G.weylPoint (longestParabolicElement G.rootBase I))⁻¹ * b *
      G.weylPoint (longestParabolicElement G.rootBase I) ∈ G.leviBorelPoints I) :
    b ∈ G.torusPoints := by
  let w := longestParabolicElement G.rootBase I
  let n := G.weylPoint w
  change n⁻¹ * b * n ∈ G.leviBorelPoints I at hc
  obtain ⟨t, ht, u, hu, he⟩ := G.leviBorel_exists_torus_mul I b hb
  have htn : n⁻¹ * t * n ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) t).mp ht
  have huB : n⁻¹ * u * n ∈ G.borelPoints := by
    have h := G.borelPoints.mul_mem (G.borelPoints.inv_mem (G.torus_le_borel htn)) hc.2
    rw [← he] at h
    convert h using 1
    group
  have huInv : u ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) := by
    simpa only [w, leftRootInv_longestParabolic] using hu
  have huOpp : n⁻¹ * u * n ∈ G.oppositeUnipotentPoints :=
    ((G.mem_inversionPoints_iff w u).mp huInv).2
  have huOne : u = 1 := by
    have hz := G.eq_one_of_oppositeUnipotent_borel _ huOpp huB
    have h := congrArg (fun a : G.points => n * a * n⁻¹) hz
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h
  rw [← he, huOne, mul_one]
  exact ht


/-- A subgroup normalized by the Levi and contained in its Borel lies in the torus. -/
theorem leviNormalPoints_le_torus (I : Set G.rootBase.support) (N : Subgroup G.points)
    (hNB : N ≤ G.leviBorelPoints I)
    (hnorm : G.leviPoints I ≤ Subgroup.normalizer (N : Set G.points)) :
    N ≤ G.torusPoints := by
  intro b hb
  apply leviBorel_mem_torus_of_conj G I b (hNB hb)
  have hnL : G.weylPoint (longestParabolicElement G.rootBase I) ∈ G.leviPoints I :=
    (G.weylPoint_mem_levi_iff I _).mpr (longestParabolicElement_mem G.rootBase I)
  apply hNB
  exact (Subgroup.mem_normalizer_iff''.mp (hnorm hnL) b).mp hb

end ReductiveGroups.ReductiveGroupData
