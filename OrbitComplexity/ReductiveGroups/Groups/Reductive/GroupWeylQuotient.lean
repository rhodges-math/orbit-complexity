import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatDisjoint
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatDoubleCosets
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Weyl representatives in the torus normalizer quotient

Multiplication of chosen representatives modulo the torus gives a homomorphism
from the root-system Weyl group into the torus normalizer quotient. A representative
in the torus lies in the Borel, so this homomorphism is injective.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The subgroup of points normalizing the chosen maximal torus. -/
abbrev torusNormalizer : Subgroup G.points := Subgroup.normalizer (G.torusPoints : Set G.points)

/-- The torus viewed as a subgroup of its normalizer. -/
abbrev torusInNormalizer : Subgroup G.torusNormalizer := G.torusPoints.subgroupOf G.torusNormalizer

/-- The torus is normal in its normalizer. -/
instance torusInNormalizer_normal : G.torusInNormalizer.Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (show G.torusNormalizer ≤
    Subgroup.normalizer (G.torusPoints : Set G.points) from le_rfl)

/-- Chosen Weyl representatives give a homomorphism into the normalizer quotient. -/
def weylQuotientMap : G.weylGroup →* G.torusNormalizer ⧸ G.torusInNormalizer where
  toFun w := QuotientGroup.mk ⟨G.weylPoint w, G.weylPoint_mem_normalizer w⟩
  map_one' := (QuotientGroup.eq_one_iff _).mpr (by
    change G.weylPoint 1 ∈ G.torusPoints
    rw [G.weylPoint_eq, weylElementPoint_one]
    exact G.torusPoints.one_mem)
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    change (G.weylPoint (a * b))⁻¹ * (G.weylPoint a * G.weylPoint b) ∈ G.torusPoints
    obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul G.rootBase a b
    have he' : G.weylPoint a * G.weylPoint b = t * G.weylPoint (a * b) := by
      simpa only [G.weylPoint_eq] using he
    rw [he']
    have h := (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer (a * b)) t).mp ht
    simpa only [mul_assoc] using h

/-- The Weyl representative homomorphism into the normalizer quotient is injective. -/
theorem weylQuotientMap_injective : Function.Injective G.weylQuotientMap := by
  intro a b hab
  have h : G.weylQuotientMap (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have ht := (QuotientGroup.eq_one_iff
    (⟨G.weylPoint (a⁻¹ * b), G.weylPoint_mem_normalizer _⟩ : G.torusNormalizer)).mp h
  change G.weylPoint (a⁻¹ * b) ∈ G.torusPoints at ht
  exact inv_mul_eq_one.mp
    (G.eq_one_of_weylPoint_mem_borel _ (G.torus_le_borel ht))

end ReductiveGroups.ReductiveGroupData
