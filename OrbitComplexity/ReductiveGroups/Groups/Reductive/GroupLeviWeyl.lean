import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFunctional
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviCharacter
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviSimple
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.FaceStabilizer
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option maxHeartbeats 400000
/-!
# Weyl representatives in a standard Levi subgroup

The central torus point and the stabilizer of a dominant integral functional
detect standard-parabolic Weyl elements. Selected reflection words prove the converse.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem functional_simple_zero (I : Set G.rootBase.support)
    (i : G.rootBase.support) :
    G.leviFunctional I (G.rootSystem.rootSpanMem ℤ i.val) = 0 ↔ i ∈ I := by
  classical
  have he : G.rootBase.toWeightBasisInt i = G.rootSystem.rootSpanMem ℤ i.val :=
    Subtype.ext (G.rootBase.coe_toWeightBasisInt_apply i)
  rw [← he, leviFunctional, Module.Basis.constr_basis]
  split_ifs <;> simp_all

private theorem functional_simple_nonneg (I : Set G.rootBase.support)
    (i : G.rootBase.support) :
    0 ≤ G.leviFunctional I (G.rootSystem.rootSpanMem ℤ i.val) := by
  classical
  have he : G.rootBase.toWeightBasisInt i = G.rootSystem.rootSpanMem ℤ i.val :=
    Subtype.ext (G.rootBase.coe_toWeightBasisInt_apply i)
  rw [← he, leviFunctional, Module.Basis.constr_basis]
  split_ifs <;> omega

omit [IsAlgClosed K] in
private theorem two_zpow_injective : Function.Injective (fun n : ℤ => (2 : K) ^ n) := by
  intro m n h
  have hQ : (2 : ℚ) ^ m = (2 : ℚ) ^ n := by
    apply Rat.cast_injective (α := K)
    simpa only [Rat.cast_zpow, Rat.cast_ofNat] using h
  exact zpow_right_injective₀ (by norm_num : 0 < (2 : ℚ)) (by norm_num) hQ

/-- A Weyl representative lies in the standard Levi exactly for a parabolic Weyl element. -/
theorem weylPoint_mem_levi_iff (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.weylPoint w ∈ G.leviPoints I ↔ w ∈ standardParabolicSubgroup G.rootBase I := by
  classical
  constructor
  · intro hw
    apply (mem_parabolic_iff_fix_functional G.rootBase I
      (G.leviFunctional I).toAddMonoidHom (functional_simple_nonneg G I)
      (functional_simple_zero G I) w).mpr
    obtain ⟨z, hzI, hzroot⟩ := G.exists_leviFunctional_point I
    intro r
    have hc := G.rootCharacter_eq_of_weyl_comm w z
      (hw (AlgHom.mapDomain G.torusSplit z) ⟨z, rfl, hzI⟩).symm r
    rw [hzroot, hzroot] at hc
    exact two_zpow_injective (K := K) hc
  · intro hw
    obtain ⟨l, hl, hword⟩ := (mem_standardParabolicSubgroup_iff_word G.rootBase I w).mp hw
    have hp : simpleWordPoint G.reflectionPoint G.rootBase l ∈ G.leviPoints I := by
      change (l.map (fun i : G.rootBase.support => G.reflectionPoint i.val)).prod ∈
        G.leviPoints I
      apply Subgroup.list_prod_mem
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      exact G.reflectionPoint_mem_levi I i (hl i hi)
    obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.simpleWordPoint_eq_mul_weylElementPoint
      G.rootBase l
    rw [hword, ← G.weylPoint_eq] at he
    have h := (G.leviPoints I).mul_mem ((G.leviPoints I).inv_mem
      (G.torus_le_leviPoints I ht)) hp
    rwa [he, inv_mul_cancel_left] at h

end ReductiveGroups.ReductiveGroupData
