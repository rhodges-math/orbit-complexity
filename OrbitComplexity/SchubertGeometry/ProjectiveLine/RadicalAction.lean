import OrbitComplexity.SchubertGeometry.ProjectiveLine.BorelGroup
import OrbitComplexity.SchubertGeometry.ProjectiveLine.Charts

/-! # The singleton parabolic radical fixes its simple Schubert variety -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem levi_le_parabolic (I : Set G.rootBase.support) :
    G.leviPoints I ≤ standardParabolicPoints G I := by
  rw [parabolic_eq_levi_sup_unipotent]
  exact le_sup_left

private theorem simple_point_representative (i : G.rootBase.support)
    (q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    ∃ p : G.points, p ∈ standardParabolicPoints G {i} ∧
      flagVarietyPointsEquiv G (flagProjection G p) =
        Variety.mapPoints
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q := by
  have hq : (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).pointMap q ∈
      Set.range (simplePositiveChart G i).left ∪ Set.range (simpleNegativeChart G i).left := by
    rw [simpleCharts_cover]
    exact Set.mem_univ _
  rcases hq with hq | hq
  · obtain ⟨a, ha⟩ := Variety.exists_mapPoints_eq (simplePositiveChart G i) q hq
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
    refine ⟨gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹, ?_, ?_⟩
    · apply levi_le_parabolic G {i}
      exact (G.leviPoints {i}).mul_mem (G.simpleRootPoint_mem_levi {i} i (by simp) t)
        ((G.leviPoints {i}).inv_mem (G.reflectionPoint_mem_levi {i} i (by simp)))
    · have he := simplePositiveChart_points G i t
      rw [Variety.mapPoints_comp, ha] at he
      exact he.symm
  · obtain ⟨a, ha⟩ := Variety.exists_mapPoints_eq (simpleNegativeChart G i) q hq
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
    refine ⟨gaParameterPoint (G.negativeSimpleRootMap i) t, ?_, ?_⟩
    · exact levi_le_parabolic G {i} (G.negativeRootPoint_mem_levi {i} i (by simp) t)
    · have he := simpleNegativeChart_points G i t
      rw [Variety.mapPoints_comp, ha] at he
      exact he.symm

private theorem radical_le_borel (I : Set G.rootBase.support) :
    parabolicUnipotentPoints G I ≤ G.borelPoints := by
  intro r hr
  exact G.unipotent_le_borel (G.rootSubsetPoints_le_unipotent _ _ hr)

private theorem radical_coset_fixed (I : Set G.rootBase.support) (r : G.points)
    (hr : r ∈ parabolicUnipotentPoints G I) (p : G.points)
    (hp : p ∈ standardParabolicPoints G I) :
    flagProjection G (r * p) = flagProjection G p := by
  apply (flagProjection_eq_iff G _ _).mpr
  have hc : p⁻¹ * r⁻¹ * p ∈ parabolicUnipotentPoints G I :=
    (Subgroup.mem_normalizer_iff''.mp (parabolicUnipotent_normalizer G I hp) r⁻¹).mp
      ((parabolicUnipotentPoints G I).inv_mem hr)
  simpa only [mul_inv_rev] using radical_le_borel G I hc

/-- The singleton parabolic unipotent radical fixes every flag of its simple Schubert variety. -/
theorem simpleRadical_flag_fixed (i : G.rootBase.support) (r : G.points)
    (hr : r ∈ parabolicUnipotentPoints G {i})
    (q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    reductivePointsMulEquiv G r •
        Variety.mapPoints
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q =
      Variety.mapPoints
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q := by
  obtain ⟨p, hp, he⟩ := simple_point_representative G i q
  rw [← he, flagVarietyAction_points, ← flagProjection_smul, radical_coset_fixed G {i} r hr p hp]

end SchubertGeometry
