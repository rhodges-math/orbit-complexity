import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositePoints
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaSubgroupParameters
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPointInjectivity
import OrbitComplexity.SchubertGeometry.FlagVariety.Points
import Mathlib.Tactic.Group

/-! # Simple-root coordinates of rank-one flags

The chosen positive and negative simple-root parameters give the two usual rank-one charts.
At a nonzero parameter the reflection chart equals the negative-root chart at its inverse.
Distinct parameters in the positive-root reflection chart determine distinct flags.

## Main results

* `flag_reflection_eq_inv`: agreement of the two simple representatives.
* `simpleRoot_flag_eq_negative`: the inverse-coordinate change between the two charts.
* `simpleRoot_flag_injective`: injectivity of the positive-root reflection chart.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- A simple reflection representative and its inverse give the same right flag. -/
theorem flag_reflection_eq_inv (i : G.rootBase.support) (g : G.points) :
    flagProjection G (g * G.reflectionPoint i.val) =
      flagProjection G (g * (G.reflectionPoint i.val)⁻¹) := by
  apply (flagProjection_eq_iff G _ _).mpr
  have hb := G.torus_le_borel
    (G.torusPoints.inv_mem (G.isBruhatSystem.rankOne i).sq_mem)
  convert hb using 1
  group
/-- The nonzero reflection-chart coordinate equals the inverse negative-root coordinate. -/
theorem simpleRoot_flag_eq_negative (i : G.rootBase.support) {m : K} (hm : m ≠ 0) :
    flagProjection G (gaParameterPoint (G.simpleRootMap i) m *
      (G.reflectionPoint i.val)⁻¹) =
        flagProjection G (gaParameterPoint (G.negativeSimpleRootMap i) m⁻¹) := by
  let h := G.isBruhatSystem.rankOne i
  obtain ⟨t, ht, hy⟩ := h.partner m⁻¹ (inv_ne_zero hm)
  simp only [inv_inv] at hy
  have hnt : G.reflectionPoint i.val * t * (G.reflectionPoint i.val)⁻¹ ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff.mp h.mem_normalizer t).mp ht
  have htn : G.reflectionPoint i.val * t * G.reflectionPoint i.val ∈ G.torusPoints := by
    convert G.torusPoints.mul_mem hnt h.sq_mem using 1
    group
  have hb := G.borelPoints.mul_mem (G.torus_le_borel htn) (h.x_mem m)
  apply (flagProjection_eq_iff G _ _).mpr
  rw [hy]
  convert hb using 1
  group

private theorem negativePoint_mem_opposite (i : G.rootBase.support) (c : K) :
    gaParameterPoint (G.negativeSimpleRootMap i) c ∈ G.oppositeUnipotentPoints := by
  apply GaParameterPoint.mem_of_tangent_mem_quotient _ _ ?_ c
  change gaAffineGroupTangent (G.negativeSimpleRootMap i) ∈ G.oppositeUnipotentTangent
  have hneg : ¬ G.rootBase.IsPos (-i.val) := by
    intro hn
    have hn' : G.rootBase.IsPos (G.rootSystem.reflectionPerm i.val i.val) := by
      simpa only [LieAlgebra.IsKilling.rootSystem_reflectionPerm_self_eq_neg] using hn
    exact (isPos_neg_index_iff G.rootBase i.val).mp hn'
      (G.rootBase.isPos_of_mem_support i.property)
  have hle : G.rootWeightSpace (-i.val) ≤ G.oppositeUnipotentTangent.toSubmodule := by
    rw [G.oppositeUnipotentTangent_eq_sum]
    exact le_iSup₂_of_le (-i.val) hneg le_rfl
  exact hle (G.negativeRootMap_tangent_mem i)

private theorem parameter_diff (i : G.rootBase.support) (a b : K) :
    (gaParameterPoint (G.simpleRootMap i) a)⁻¹ * gaParameterPoint (G.simpleRootMap i) b =
      gaParameterPoint (G.simpleRootMap i) (b - a) := by
  change (gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd a))⁻¹ *
    gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd b) =
      gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (b - a))
  rw [← map_inv, ← map_mul]
  congr 1
  change Multiplicative.ofAdd (-a + b) = Multiplicative.ofAdd (b - a)
  congr 1
  abel

/-- Distinct positive simple-root parameters determine distinct flags in the reflection chart. -/
theorem simpleRoot_flag_injective (i : G.rootBase.support) :
    Function.Injective (fun m : K => flagProjection G
      (gaParameterPoint (G.simpleRootMap i) m * (G.reflectionPoint i.val)⁻¹)) := by
  intro a b hab
  have hB := (flagProjection_eq_iff G _ _).mp hab
  have hdiff : (gaParameterPoint (G.simpleRootMap i) a * (G.reflectionPoint i.val)⁻¹)⁻¹ *
        (gaParameterPoint (G.simpleRootMap i) b * (G.reflectionPoint i.val)⁻¹) =
      G.reflectionPoint i.val * gaParameterPoint (G.simpleRootMap i) (b - a) *
        (G.reflectionPoint i.val)⁻¹ := by
    rw [← parameter_diff G i a b]
    group
  rw [hdiff] at hB
  obtain ⟨c, hc⟩ := (G.isBruhatSystem.rankOne i).conj_x (b - a)
  rw [hc] at hB
  have hy := G.eq_one_of_oppositeUnipotent_borel _ (negativePoint_mem_opposite G i c) hB
  have hconj := hc.trans hy
  have hx : gaParameterPoint (G.simpleRootMap i) (b - a) = 1 := by
    apply (MulAut.conj (G.reflectionPoint i.val)).injective
    exact hconj.trans (map_one _).symm
  have habPoint := inv_mul_eq_one.mp ((parameter_diff G i a b).trans hx)
  exact congrArg Multiplicative.toAdd
    (GaAffineGroupPoints.injective_of_tangent_ne_zero (G.simpleRootMap i)
      (G.simpleRootMap_tangent_ne_zero i) habPoint)

end SchubertGeometry
