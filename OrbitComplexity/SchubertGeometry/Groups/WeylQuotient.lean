import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelNormalizer
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupWeylQuotient

/-!
# The Weyl group as the torus normalizer quotient

A normalizer point fixes its flag under the torus. In the unique inversion-root
normal form, this forces the unipotent factor to centralize the torus and hence
to be the identity. Every normalizer class is therefore represented by the fixed
Weyl representative, giving the normalizer-quotient identification.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertGeometry
open ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem normalizer_mem_weyl_torus (n : G.torusNormalizer) :
    ∃ w : G.weylGroup, (G.weylPoint w)⁻¹ * n.val ∈ G.torusPoints := by
  obtain ⟨w, u, hu⟩ := flagPoint_normalForm G (flagProjection G n.val)
  have hcomm : ∀ t ∈ G.torusPoints, t * u.val = u.val * t := by
    intro t ht
    let v : schubertUnipotentPoints G w := ⟨t * u.val * t⁻¹,
      G.rootSubsetPoints_conjugate_mem _ _ t u.val ht u.property⟩
    have hleft : schubertPointMap G w v = t • schubertPointMap G w u := by
      change flagProjection G ((t * u.val * t⁻¹) * G.weylPoint w) =
        flagProjection G (t * (u.val * G.weylPoint w))
      apply (flagProjection_eq_iff G _ _).mpr
      have hT := (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) t).mp ht
      convert G.torus_le_borel hT using 1
      group
    have hfix : t • flagProjection G n.val = flagProjection G n.val := by
      change flagProjection G (t * n.val) = flagProjection G n.val
      apply (flagProjection_eq_iff G _ _).mpr
      have hT := (Subgroup.mem_normalizer_iff''.mp n.property t⁻¹).mp
        (G.torusPoints.inv_mem ht)
      simpa only [mul_inv_rev, mul_assoc] using G.torus_le_borel hT
    have hvu : v = u := (schubertPointMap_injective G w) (by rw [hleft, hu, hfix])
    have hc : t * u.val * t⁻¹ = u.val := congrArg Subtype.val hvu
    exact (mul_inv_eq_iff_eq_mul).mp hc
  have hu1 := G.unipotent_eq_one_of_centralizes u.val
    (G.rootSubsetPoints_le_unipotent _ _ u.property) hcomm
  have hflag : flagProjection G (G.weylPoint w) = flagProjection G n.val := by
    simpa only [schubertPointMap, hu1, one_mul] using hu
  have hB : (G.weylPoint w)⁻¹ * n.val ∈ G.borelPoints :=
    (flagProjection_eq_iff G _ _).mp hflag
  have hN : (G.weylPoint w)⁻¹ * n.val ∈ G.torusNormalizer :=
    G.torusNormalizer.mul_mem (G.torusNormalizer.inv_mem (G.weylPoint_mem_normalizer w))
      n.property
  refine ⟨w, ?_⟩
  have h : (G.weylPoint w)⁻¹ * n.val ∈ G.borelPoints ⊓ G.torusNormalizer := ⟨hB, hN⟩
  rwa [G.borel_inf_torus_normalizer] at h

/-- Every torus-normalizer class is represented by a Weyl element. -/
theorem weylQuotientMap_surjective : Function.Surjective G.weylQuotientMap := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H n =>
    obtain ⟨w, hw⟩ := normalizer_mem_weyl_torus G n
    refine ⟨w, QuotientGroup.eq.mpr ?_⟩
    change (G.weylPoint w)⁻¹ * n.val ∈ G.torusPoints
    exact hw

/-- The root-system Weyl group is the maximal-torus normalizer modulo the torus. -/
def weylQuotientEquiv : G.weylGroup ≃* G.torusNormalizer ⧸ G.torusInNormalizer :=
  MulEquiv.ofBijective G.weylQuotientMap
    ⟨G.weylQuotientMap_injective, weylQuotientMap_surjective G⟩

/-- The normalizer-quotient identification uses the fixed Weyl representative. -/
theorem weylQuotientEquiv_apply (w : G.weylGroup) :
    weylQuotientEquiv G w = QuotientGroup.mk
      (⟨G.weylPoint w, G.weylPoint_mem_normalizer w⟩ : G.torusNormalizer) := rfl

end SchubertGeometry
