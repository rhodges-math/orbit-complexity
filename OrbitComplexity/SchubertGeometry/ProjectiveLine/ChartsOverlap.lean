import OrbitComplexity.SchubertGeometry.ProjectiveLine.Charts

/-! # The overlap of the simple-root charts

The positive and negative chart origins are different flags. Their rational images
therefore intersect precisely at the nonzero additive parameters.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
private theorem simpleCharts_zero_ne (i : G.rootBase.support) :
    Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K 0) ≠
      Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0) := by
  intro he
  have hf := congrArg (Variety.mapPoints
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) he
  rw [← Variety.mapPoints_comp, ← Variety.mapPoints_comp, simplePositiveChart_points,
    simpleNegativeChart_points, gaParameterPoint_zero, gaParameterPoint_zero, one_mul] at hf
  have hz := (flagVarietyPointsEquiv G).injective hf
  rw [simpleRepresentative_flag] at hz
  have hb : G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val) ∈ G.borelPoints := by
    simpa only [inv_one, one_mul] using (flagProjection_eq_iff G _ _).mp hz.symm
  have hs := G.eq_one_of_weylPoint_mem_borel _ hb
  have hl := congrArg (weylCoxeterSystem G.rootBase).length hs
  rw [← weylCoxeterSystem_simple, CoxeterSystem.length_simple,
    CoxeterSystem.length_one] at hl
  exact Nat.one_ne_zero hl

/-- A positive-chart parameter lies in the negative chart exactly when it is nonzero. -/
theorem simpleCharts_overlap (i : G.rootBase.support) (t : K) :
    Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) ∈
      Set.range (Variety.mapPoints (simpleNegativeChart G i)) ↔ t ≠ 0 := by
  constructor
  · rintro ⟨p, hp⟩ ht
    obtain ⟨c, rfl⟩ := (additivePointsEquiv K).surjective p
    subst t
    by_cases hc : c = 0
    · subst c
      exact simpleCharts_zero_ne G i hp.symm
    · have he := simpleCharts_transition G i (inv_ne_zero hc)
      rw [inv_inv] at he
      have hi := Variety.mapPoints_injective_of_mono (simplePositiveChart G i) (he.trans hp)
      exact inv_ne_zero hc ((additivePointsEquiv K).injective hi)
  · intro ht
    exact ⟨additivePointsEquiv K t⁻¹, (simpleCharts_transition G i ht).symm⟩
end SchubertGeometry
